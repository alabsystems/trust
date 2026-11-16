// ignore-tidy-file-filelength -- pre-existing size, recorded 2026-10-17; do not grow casually
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The L1→L2 spec elaborator (two-language design §5): surface contract
//! clauses → `clean_kernel::Expr` goals, then prove (clean-auto portfolio)
//! and certify (the honesty meter).
//!
//! ```text
//!   L1 surface     "0 + x == x"                           (a Rust spec predicate)
//!   L2 elaborate ─▶ ∀ (x : Nat), Eq Nat (Nat.add 0 x) x   (a CIC goal)
//!   L4 tactic    ─▶ clean-auto proves it (SMT or Nat.rec) (a proof term)
//!   L5 kernel    ─▶ check_type(term, goal) + trust-marker gate → Certified
//! ```
//!
//! Ported bin→lib from the reference spike
//! (`first-party/trust-wp/spikes/clean-spec-elaborate`) at the R4 landing —
//! the elaborator is toolchain infrastructure serving every engine, so it
//! lives in trust proper. The supported scalar vocabulary evolves with the
//! kernel prelude; its exact domains, operators, and fail-closed boundaries are
//! recorded in `docs/design-notes/2026-07-15-spec-elaboration-fragment.md`.
//! E3 additionally admits one clause-head `forall`/`exists` binder and
//! right-associative `==>` implication; nested and multi-binder forms remain
//! fail-closed.
//! Unsupported syntax is always an elaboration error, never silently dropped.
//! Elaboration is total over the admitted structure; proof stays gradual (a
//! goal may elaborate yet remain Pending if the auto-fragment cannot discharge
//! it).

use std::borrow::Cow;
use std::collections::{BTreeMap, BTreeSet};
use std::time::Duration;

use cert_meter::Grade;
use clean_auto::AutomationEngine;
use clean_kernel::expr::BinderInfo;
use clean_kernel::{Declaration, Environment, Expr, Level, Name};
use syn::{BinOp, Expr as SynExpr, Lit};
// I2: the one vocabulary that says whether a kernel constant is a reflected
// Rust carrier or a kernel-re-checked Clean declaration.
use trust_symbols::KernelStatus;

mod registered_carrier;
pub use registered_carrier::{
    AdtSchema, ConstructorSchema, RegisteredAdt, canonical_declaration_binding,
    canonical_environment_binding,
};
#[cfg(test)]
mod registered_domain_tests;

// Trust (E9-ODT-FACE-SELF-CALL-1): the self-call over a nominal ODT import.
mod odt_face_self_call;

// Trust (E6 admission expansion I3′): the E6-only TREE producer.
mod e6_tree;
pub use e6_tree::{E6TreeArith, E6TreeCmp, E6TreeTerm, admit_e6_tree_function};

// The same actual-body reader/renderer serves E6 intake and emitted-body gates.
pub mod e6_import;
pub use e6_import::admit_e6_only_body;

fn nat() -> Expr {
    Expr::const_(Name::interned("Nat"), vec![])
}

/// One supported fixed-width unsigned machine carrier.
///
/// This closed enum is deliberate: accepting an arbitrary constant name (or
/// target-dependent `usize`) would let a caller construct a goal whose carrier
/// is absent or whose width is not bound to the compilation target.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MachineUIntWidth {
    U8,
    U16,
    U32,
    U64,
}

impl MachineUIntWidth {
    const fn carrier(self) -> &'static str {
        match self {
            Self::U8 => "UInt8",
            Self::U16 => "UInt16",
            Self::U32 => "UInt32",
            Self::U64 => "UInt64",
        }
    }

    const fn to_nat_const(self) -> &'static str {
        match self {
            Self::U8 => "UInt8.toNat",
            Self::U16 => "UInt16.toNat",
            Self::U32 => "UInt32.toNat",
            Self::U64 => "UInt64.toNat",
        }
    }

    const fn of_nat_const(self) -> &'static str {
        match self {
            Self::U8 => "UInt8.ofNat",
            Self::U16 => "UInt16.ofNat",
            Self::U32 => "UInt32.ofNat",
            Self::U64 => "UInt64.ofNat",
        }
    }

    const fn dec_eq_const(self) -> &'static str {
        match self {
            Self::U8 => "UInt8.decEq",
            Self::U16 => "UInt16.decEq",
            Self::U32 => "UInt32.decEq",
            Self::U64 => "UInt64.decEq",
        }
    }

    const fn inst_lt_const(self) -> &'static str {
        match self {
            Self::U8 => "instLTUInt8",
            Self::U16 => "instLTUInt16",
            Self::U32 => "instLTUInt32",
            Self::U64 => "instLTUInt64",
        }
    }

    const fn inst_le_const(self) -> &'static str {
        match self {
            Self::U8 => "instLEUInt8",
            Self::U16 => "instLEUInt16",
            Self::U32 => "instLEUInt32",
            Self::U64 => "instLEUInt64",
        }
    }

    const fn inst_decidable_lt_const(self) -> &'static str {
        match self {
            Self::U8 => "instDecidableUInt8Lt",
            Self::U16 => "instDecidableUInt16Lt",
            Self::U32 => "instDecidableUInt32Lt",
            Self::U64 => "instDecidableUInt64Lt",
        }
    }

    const fn inst_decidable_le_const(self) -> &'static str {
        match self {
            Self::U8 => "instDecidableUInt8Le",
            Self::U16 => "instDecidableUInt16Le",
            Self::U32 => "instDecidableUInt32Le",
            Self::U64 => "instDecidableUInt64Le",
        }
    }

    const fn inst_decidable_eq_const(self) -> &'static str {
        match self {
            Self::U8 => "instDecidableEqUInt8",
            Self::U16 => "instDecidableEqUInt16",
            Self::U32 => "instDecidableEqUInt32",
            Self::U64 => "instDecidableEqUInt64",
        }
    }

    /// The bit width — the exclusive upper bound on a valid shift amount (Rust
    /// rejects a shift `>=` the width).
    const fn bits(self) -> u32 {
        match self {
            Self::U8 => 8,
            Self::U16 => 16,
            Self::U32 => 32,
            Self::U64 => 64,
        }
    }

    /// The largest value representable at this width — the inclusive upper
    /// bound a spec literal may take before it is out of range for the type.
    const fn max_value(self) -> u128 {
        match self {
            Self::U8 => u8::MAX as u128,
            Self::U16 => u16::MAX as u128,
            Self::U32 => u32::MAX as u128,
            Self::U64 => u64::MAX as u128,
        }
    }

    /// The Rust source type name (`u8` …) — used in diagnostics so the message
    /// names the type the user wrote, not the Clean carrier (`UInt8`).
    const fn rust_name(self) -> &'static str {
        match self {
            Self::U8 => "u8",
            Self::U16 => "u16",
            Self::U32 => "u32",
            Self::U64 => "u64",
        }
    }
}

/// A supported fixed-width signed Rust machine carrier.
///
/// Clean's native prelude intentionally does not seed the wrapper types
/// `Int8`…`Int64`.  Trust therefore represents these values by their exact
/// two's-complement bit pattern in `BitVec <width>`.  This enum is closed so no
/// caller can accidentally request a width the runtime evaluator or kernel
/// projection does not implement.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MachineSIntWidth {
    I8,
    I16,
    I32,
    I64,
    I128,
}

impl MachineSIntWidth {
    const fn bits(self) -> u32 {
        match self {
            Self::I8 => 8,
            Self::I16 => 16,
            Self::I32 => 32,
            Self::I64 => 64,
            Self::I128 => 128,
        }
    }

    const fn rust_name(self) -> &'static str {
        match self {
            Self::I8 => "i8",
            Self::I16 => "i16",
            Self::I32 => "i32",
            Self::I64 => "i64",
            Self::I128 => "i128",
        }
    }

    const fn signed_lift_const(self) -> &'static str {
        match self {
            Self::I8 => "trust_checked_toInt8",
            Self::I16 => "trust_checked_toInt16",
            Self::I32 => "trust_checked_toInt32",
            Self::I64 => "trust_checked_toInt64",
            Self::I128 => "trust_checked_toInt128",
        }
    }

    const fn signed_fits_const(self) -> &'static str {
        match self {
            Self::I8 => "trust_checked_fitsI8",
            Self::I16 => "trust_checked_fitsI16",
            Self::I32 => "trust_checked_fitsI32",
            Self::I64 => "trust_checked_fitsI64",
            Self::I128 => "trust_checked_fitsI128",
        }
    }
}

/// A compilation target's resolved pointer width.
///
/// Bare `usize`/`isize` bindings are never guessed.  Compiler callers either
/// use [`certify_monitor_typed_for_target`] (which supplies this value
/// separately) or pass the explicit compatibility spellings
/// `usize16`/`usize32`/`usize64` and `isize16`/`isize32`/`isize64`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TargetPointerWidth {
    W16,
    W32,
    W64,
}

impl TargetPointerWidth {
    /// Construct a supported target pointer width.
    pub fn from_bits(bits: u32) -> Result<Self, String> {
        match bits {
            16 => Ok(Self::W16),
            32 => Ok(Self::W32),
            64 => Ok(Self::W64),
            _ => Err(format!("unsupported target pointer width {bits} (supported: 16, 32, or 64)")),
        }
    }

    /// The resolved number of target pointer bits.
    #[must_use]
    pub const fn bits(self) -> u32 {
        match self {
            Self::W16 => 16,
            Self::W32 => 32,
            Self::W64 => 64,
        }
    }
}

/// The clause-binder spelling at which the E9 DISCHARGE lanes (cited
/// `ensures … by thm`, uncited island defeq, and the citation sweep) bind one
/// resolved Rust scalar type name on a target whose pointer width is
/// `pointer_width`.
///
/// Every name except bare `usize`/`isize` is returned unchanged. Those two are
/// resolved to the fixed-width machine spelling of the SAME width and
/// signedness: `usize` on a 64-bit target binds exactly as `u64` (Clean carrier
/// `UInt64`), `isize` exactly as `i64` (`BitVec 64` under the signed order key).
///
/// WHY NOT `usize64` (`Domain::USize`, carrier `BitVec 64`). A discharge goal
/// applies the function's E6 kernel import to the clause binders
/// ([`elaborate_ensures`] substitutes `result` with `self_fn(params…)`), and an
/// admitted call is checked against the callee's DECLARED carriers, never
/// coerced. The import is minted from the extracted body — and there are TWO
/// extraction spellings of a pointer-sized integer, of which only the first
/// feeds this lane. The verifier's extraction
/// (`trust_mir_extract::extract_function_with_contract_bundle`, the lane whose
/// bodies the E6 mint accumulates) collapses `usize`/`isize` to
/// `Int { width: <target pointer width>, .. }`, so its carrier is `UInt64` on a
/// 64-bit target — the same as `u64` — and `UInt32` on a 32-bit one. The
/// FAITHFUL extraction (`trust_mir_extract::extract_function_faithful`, v25 B1,
/// the trust-ir differential's lane) keeps `PtrSizedInt { signed }` instead,
/// which `trust_certify::clean_island`'s `ty_to_domain` maps to `Machine(U64)`
/// with the `64` HARD-CODED, and for which it has no signed case at all. So the
/// carrier agreement this resolution rests on is the FIRST spelling's, where the
/// width is the target's and the argument holds at every width this elaborator
/// models; through the faithful spelling it would hold only at 64 bits, and
/// `isize` would fail closed. The 2026-09-15 forwarding mint
/// ([`admit_forwarding_function`]) does not weaken that: it takes the import's
/// carriers from the callee's kernel-checked Clean declaration and requires the
/// extracted parameter domains to AGREE with them before minting, so a target
/// whose extracted `usize` carrier is not the declared one refuses the mint
/// outright rather than coercing it. A `usize64` binder would type every
/// `result`-mentioning clause on a
/// `usize` function at `BitVec 64` against a `UInt64` import and be refused,
/// which is precisely the form contracts on `usize` functions take. The
/// statement-only lanes (runtime monitors, zero-authority denotation rows)
/// apply no import and keep the `usize64` spelling.
///
/// SOUNDNESS. On a target of pointer width `w`, Rust's `usize` has exactly
/// `uw`'s value range, wrapping arithmetic and order, so a clause over `usize`
/// binders means the same thing read over `uw` binders. The width is the
/// CALLER'S resolved target width, never the host's and never a default: a
/// theorem stated over `UInt64` closes a `usize` clause only on a 64-bit
/// target, and on a 32-bit target the goal quantifies over `UInt32`, which that
/// proof term does not inhabit — the citation is a hard statement mismatch
/// there, not a silently narrower claim. A width this elaborator does not model
/// cannot be constructed ([`TargetPointerWidth::from_bits`] refuses it), and a
/// caller that cannot resolve one must pass the bare name through unchanged so
/// the binding gate keeps refusing it.
#[must_use]
pub fn discharge_binding_ty_for_target(name: &str, pointer_width: TargetPointerWidth) -> &str {
    match (name, pointer_width) {
        ("usize", TargetPointerWidth::W16) => "u16",
        ("usize", TargetPointerWidth::W32) => "u32",
        ("usize", TargetPointerWidth::W64) => "u64",
        ("isize", TargetPointerWidth::W16) => "i16",
        ("isize", TargetPointerWidth::W32) => "i32",
        ("isize", TargetPointerWidth::W64) => "i64",
        _ => name,
    }
}

fn kernel_nat_lit(n: u128) -> Expr {
    match u64::try_from(n) {
        Ok(n) => Expr::nat_lit(n),
        Err(_) => Expr::nat_lit_u128(n),
    }
}

// Bootstrap rustc cannot parse Trust's native signature clauses, while the
// verified lane must retain those exact clause tokens. Each invocation below
// owns its function body once. Trust injects `cfg(trust_verify)` only while
// verification is active, selecting the native-clause expansion; an ordinary
// compiler emits the same function and body without the clauses. build.rs only
// registers the cfg name for stock Cargo's check-cfg lint; it never selects it.
// (The same mechanism as `trust-budget`, `trust-intbound`, `trust-widthconv`
// and `trust-floatbits`.)
#[cfg(trust_verify)]
macro_rules! trust_contract_fn {
    (
        $(#[$meta:meta])*
        $vis:vis fn $name:ident($($arg:ident : $arg_ty:ty),* $(,)?) -> $ret:ident
        clauses [$($clauses:tt)+]
        { $($body:tt)* }
    ) => {
        $(#[$meta])*
        $vis fn $name($($arg: $arg_ty),*) -> $ret
            $($clauses)+
        { $($body)* }
    };
}

#[cfg(not(trust_verify))]
macro_rules! trust_contract_fn {
    (
        $(#[$meta:meta])*
        $vis:vis fn $name:ident($($arg:ident : $arg_ty:ty),* $(,)?) -> $ret:ident
        clauses [$($clauses:tt)+]
        { $($body:tt)* }
    ) => {
        $(#[$meta])*
        $vis fn $name($($arg: $arg_ty),*) -> $ret { $($body)* }
    };
}

trust_contract_fn! {
/// The all-ones mask of a `bits`-wide carrier.
///
/// `bits` is the width of a closed BitVec carrier, so it lies in `1..=128`:
/// the shift below is defined only below 128 and the 128-bit mask is the whole
/// word. That range used to be an UNSTATED precondition — the verifier refuted
/// the shift at `bits = 129` (measured 2026-09-13 on driver `dff2b22d1`) — and
/// is now a `requires` that every caller establishes on the line before the
/// call, because a width that reaches this function through an `Option`
/// accessor is an opaque value to the verifier until it is compared.
fn bit_mask(bits: u32) -> u128
clauses [requires bits <= 128]
{
    if bits == 128 { u128::MAX } else { (1u128 << bits) - 1 }
}
}

trust_contract_fn! {
/// `2^(bits-1) - 1`: the largest non-negative value of a `bits`-wide two's
/// complement carrier. Width range as at [`bit_mask`]; `bits >= 1` is what
/// keeps `bits - 1` from underflowing (refuted at `bits = 0` before).
fn signed_positive_max(bits: u32) -> u128
clauses [requires bits >= 1 requires bits <= 128]
{
    (1u128 << (bits - 1)) - 1
}
}

trust_contract_fn! {
/// `2^(bits-1)`: the magnitude of the most negative value of a `bits`-wide
/// two's complement carrier. Width range as at [`bit_mask`].
fn signed_negative_magnitude_max(bits: u32) -> u128
clauses [requires bits >= 1 requires bits <= 128]
{
    1u128 << (bits - 1)
}
}

/// The arithmetic domain of a statement elaborated by this crate.
///
/// This is statement-level kernel input only. It carries no Rust/Trust-IR
/// obligation identity and therefore cannot, by itself, discharge or grade a
/// Rust VC. Authority requires a future caller to derive the bindings from a
/// canonical typed Trust-IR obligation and bind the checked theorem to that
/// obligation's semantic digest.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Domain {
    /// Unbounded `Nat`.
    Nat,
    /// Unbounded `Int` — the SECOND math domain, and the codomain of the
    /// nat-lift table's signed and `Int`-targeted rows.
    ///
    /// Deliberately NOT a binding type: [`Self::from_binding_ty`] maps
    /// `"nat"`/`"Nat"` and nothing maps to `Int`, so a clause binder can never
    /// be declared at `Int`. The only ways into this domain are an explicit
    /// `e as int` cast in a PROOF-position clause and an island definition
    /// whose declared codomain is `Int`. That asymmetry is on purpose: `nat`
    /// predates this work as a ratified binder spelling, while an `int` BINDER
    /// would be a new authoritative surface spelling, which is the owner's to
    /// ratify, not this lane's.
    ///
    /// It carries NO runtime monitor carrier (like [`Domain::OptionSigned`]):
    /// a clause that reaches `Int` is kernel-goal-only and reports
    /// `unmonitored` rather than minting an executable check.
    Int,
    /// A fixed-width unsigned machine integer with wrapping arithmetic.
    Machine(MachineUIntWidth),
    /// A fixed-width signed machine integer, represented by an exact
    /// two's-complement `BitVec`.
    Signed(MachineSIntWidth),
    /// Rust `u128`, represented by `BitVec 128`.
    U128,
    /// Rust `usize` after the compiler has explicitly fixed the target width.
    USize(TargetPointerWidth),
    /// Rust `isize` after the compiler has explicitly fixed the target width.
    ISize(TargetPointerWidth),
    /// `bool`. A logical domain — no arithmetic and no ordering; only
    /// equality, the boolean connectives, and a bare variable used as a
    /// proposition (`flag` ≡ `flag = true`). It is a per-ATOM domain: a clause
    /// may freely mix `bool` and arithmetic atoms across connectives
    /// (`flag && x < 10`); only the operands of a SINGLE comparison must share a
    /// type (see [`atom_domain`]).
    Bool,
    /// `Option<iN>` — the RESULT carrier of an admitted overflow-checked
    /// signed arithmetic function (`checked_add`/`checked_sub`/`checked_mul`).
    /// Its Clean carrier is the native `Option (BitVec N)`.
    ///
    /// A CONSTRUCTOR-ONLY domain, by design (checked-arith spec §3.3/§3.4):
    /// the only term formers are `Some(e)` (the inner term at the SIGNED
    /// carrier) and `None`, plus a call to an admitted function whose recorded
    /// return domain is this carrier; the only relation is homogeneous
    /// equality. There is NO arithmetic, NO ordering, NO order key, NO
    /// numeral, and NO destructor — every such site below answers fail-closed,
    /// and the exhaustive matches are the checklist that keeps a future
    /// variant honest.
    OptionSigned(MachineSIntWidth),
    /// An exact, checked kernel datatype application. This transports a
    /// mathematical carrier, not a Rust representation or a body proof.
    /// Use the environment-aware typed entry points to revalidate it.
    RegisteredAdt(RegisteredAdt),
}

impl Domain {
    /// Map one explicit binding type to its Clean carrier, if supported.
    ///
    /// Bare `usize`/`isize` remain hard failures because they do not identify a
    /// target width.  The compatibility spellings `usize16`/`usize32`/`usize64`
    /// and `isize16`/`isize32`/`isize64` are already resolved and therefore safe. Compiler
    /// code should normally use [`Self::from_binding_ty_for_target`] through
    /// the public target-aware certification entry points instead.
    fn from_binding_ty(name: &str) -> Option<Self> {
        Some(match name {
            "u8" => Domain::Machine(MachineUIntWidth::U8),
            "u16" => Domain::Machine(MachineUIntWidth::U16),
            "u32" => Domain::Machine(MachineUIntWidth::U32),
            "u64" => Domain::Machine(MachineUIntWidth::U64),
            "u128" => Domain::U128,
            "i8" => Domain::Signed(MachineSIntWidth::I8),
            "i16" => Domain::Signed(MachineSIntWidth::I16),
            "i32" => Domain::Signed(MachineSIntWidth::I32),
            "i64" => Domain::Signed(MachineSIntWidth::I64),
            "i128" => Domain::Signed(MachineSIntWidth::I128),
            "usize16" => Domain::USize(TargetPointerWidth::W16),
            "usize32" => Domain::USize(TargetPointerWidth::W32),
            "usize64" => Domain::USize(TargetPointerWidth::W64),
            "isize16" => Domain::ISize(TargetPointerWidth::W16),
            "isize32" => Domain::ISize(TargetPointerWidth::W32),
            "isize64" => Domain::ISize(TargetPointerWidth::W64),
            "nat" | "Nat" => Domain::Nat,
            "bool" => Domain::Bool,
            _ => return None,
        })
    }

    fn from_binding_ty_for_target(name: &str, pointer_width: TargetPointerWidth) -> Option<Self> {
        match name {
            "usize" => Some(Domain::USize(pointer_width)),
            "isize" => Some(Domain::ISize(pointer_width)),
            "usize16" if pointer_width != TargetPointerWidth::W16 => None,
            "usize32" if pointer_width != TargetPointerWidth::W32 => None,
            "usize64" if pointer_width != TargetPointerWidth::W64 => None,
            "isize16" if pointer_width != TargetPointerWidth::W16 => None,
            "isize32" if pointer_width != TargetPointerWidth::W32 => None,
            "isize64" if pointer_width != TargetPointerWidth::W64 => None,
            _ => Self::from_binding_ty(name),
        }
    }

    fn bitvec_bits(&self) -> Option<u32> {
        match self {
            Domain::OptionSigned(_) | Domain::RegisteredAdt(_) => None,
            Domain::Signed(width) => Some(width.bits()),
            Domain::U128 => Some(128),
            Domain::USize(width) | Domain::ISize(width) => Some(width.bits()),
            Domain::Nat | Domain::Int | Domain::Machine(_) | Domain::Bool => None,
        }
    }

    fn is_signed(&self) -> bool {
        matches!(self, Domain::Signed(_) | Domain::ISize(_))
    }

    /// Whether this domain has NEGATIVE values a clause may spell.
    ///
    /// [`Self::is_signed`] answers "is a two's-complement machine carrier",
    /// which is what the BitVec helpers key on; this answers the different
    /// question the literal and unary-negation sites ask, and [`Domain::Int`]
    /// is the one domain where the two answers differ.
    fn admits_negative_values(&self) -> bool {
        self.is_signed() || matches!(self, Domain::Int)
    }

    /// Whether this is one of the two UNBOUNDED math domains — the codomains
    /// of the nat-lift table (§3.1 of the nat-lift design).
    fn is_math(&self) -> bool {
        match self {
            Domain::Nat | Domain::Int => true,
            Domain::Machine(_)
            | Domain::Signed(_)
            | Domain::U128
            | Domain::USize(_)
            | Domain::ISize(_)
            | Domain::Bool
            | Domain::OptionSigned(_)
            | Domain::RegisteredAdt(_) => false,
        }
    }

    fn rust_name(&self) -> &'static str {
        match self {
            Domain::RegisteredAdt(_) => "registered kernel datatype",
            Domain::OptionSigned(MachineSIntWidth::I8) => "Option<i8>",
            Domain::OptionSigned(MachineSIntWidth::I16) => "Option<i16>",
            Domain::OptionSigned(MachineSIntWidth::I32) => "Option<i32>",
            Domain::OptionSigned(MachineSIntWidth::I64) => "Option<i64>",
            Domain::OptionSigned(MachineSIntWidth::I128) => "Option<i128>",
            Domain::Nat => "nat",
            Domain::Int => "int",
            Domain::Machine(width) => width.rust_name(),
            Domain::Signed(width) => width.rust_name(),
            Domain::U128 => "u128",
            Domain::USize(TargetPointerWidth::W16) => "usize (16-bit target)",
            Domain::USize(TargetPointerWidth::W32) => "usize (32-bit target)",
            Domain::USize(TargetPointerWidth::W64) => "usize (64-bit target)",
            Domain::ISize(TargetPointerWidth::W16) => "isize (16-bit target)",
            Domain::ISize(TargetPointerWidth::W32) => "isize (32-bit target)",
            Domain::ISize(TargetPointerWidth::W64) => "isize (64-bit target)",
            Domain::Bool => "bool",
        }
    }

    fn bitvec_width_expr(&self) -> Result<Expr, String> {
        self.bitvec_bits()
            .map(|bits| Expr::nat_lit(u64::from(bits)))
            .ok_or_else(|| format!("`{}` is not represented by a BitVec", self.rust_name()))
    }

    fn bitvec_to_nat(&self, value: Expr) -> Result<Expr, String> {
        Ok(Expr::apps(
            Expr::const_(Name::interned("BitVec.toNat"), vec![]),
            [self.bitvec_width_expr()?, value],
        ))
    }

    fn bitvec_of_nat(&self, value: Expr) -> Result<Expr, String> {
        Ok(Expr::apps(
            Expr::const_(Name::interned("BitVec.ofNat"), vec![]),
            [self.bitvec_width_expr()?, value],
        ))
    }

    fn bitvec_order_key(&self, value: Expr) -> Result<Expr, String> {
        let bits = self
            .bitvec_bits()
            .ok_or_else(|| format!("`{}` is not represented by a BitVec", self.rust_name()))?;
        // The width arrives through an `Option`, which the verifier reads as an
        // opaque call result: restate the closed carrier range on the line
        // before the shift so `bits - 1` and `1 << (bits - 1)` discharge
        // (measured 2026-09-13 on `dff2b22d1`: refuted at 0 and 129 without it).
        if bits < 1 || bits > 128 {
            return Err(format!(
                "`{}` has BitVec width {bits}; the width helpers accept 1..=128",
                self.rust_name()
            ));
        }
        let nat_value = self.bitvec_to_nat(value)?;
        if self.is_signed() {
            // Flipping the sign bit maps two's-complement signed order to
            // ordinary unsigned order, bijectively:
            //   MIN..-1 ↦ 0..2^(w-1)-1, 0..MAX ↦ 2^(w-1)..2^w-1.
            Ok(Expr::apps(
                Expr::const_(Name::interned("Nat.xor"), vec![]),
                [nat_value, kernel_nat_lit(1u128 << (bits - 1))],
            ))
        } else {
            Ok(nat_value)
        }
    }

    /// The executable runtime carrier for this domain. The closed
    /// [`MachineUIntWidth`] enum means every machine domain that can be
    /// elaborated also has an exact runtime carrier; target-dependent `usize`
    /// already fails closed at binding time (`from_binding_ty`), so a monitor
    /// can never be minted for a width the target does not pin.
    fn runtime_domain(&self) -> Result<RuntimeMonitorDomain, String> {
        match self {
            Domain::RegisteredAdt(_) => Err(self.registered_operation_refusal("runtime monitoring")),
            Domain::OptionSigned(_) => Err(format!(
                "`{}` has no runtime monitor carrier (Option results are \
                 kernel-goal-only)",
                self.rust_name()
            )),
            // `Int` is kernel-goal-only, exactly like the Option carrier above
            // it: the lift table's codomain has no executable Rust twin, so a
            // clause that reaches it reports `unmonitored` rather than minting
            // a monitor at some guessed width.
            Domain::Int => Err(
                "`int` has no runtime monitor carrier (a lifted clause is kernel-goal-only)"
                    .to_string(),
            ),
            Domain::Nat => Ok(RuntimeMonitorDomain::Nat),
            Domain::Machine(MachineUIntWidth::U8) => Ok(RuntimeMonitorDomain::U8),
            Domain::Machine(MachineUIntWidth::U16) => Ok(RuntimeMonitorDomain::U16),
            Domain::Machine(MachineUIntWidth::U32) => Ok(RuntimeMonitorDomain::U32),
            Domain::Machine(MachineUIntWidth::U64) => Ok(RuntimeMonitorDomain::U64),
            Domain::Signed(MachineSIntWidth::I8) => Ok(RuntimeMonitorDomain::I8),
            Domain::Signed(MachineSIntWidth::I16) => Ok(RuntimeMonitorDomain::I16),
            Domain::Signed(MachineSIntWidth::I32) => Ok(RuntimeMonitorDomain::I32),
            Domain::Signed(MachineSIntWidth::I64) => Ok(RuntimeMonitorDomain::I64),
            Domain::Signed(MachineSIntWidth::I128) => Ok(RuntimeMonitorDomain::I128),
            Domain::U128 => Ok(RuntimeMonitorDomain::U128),
            Domain::USize(TargetPointerWidth::W16) => Ok(RuntimeMonitorDomain::USize16),
            Domain::USize(TargetPointerWidth::W32) => Ok(RuntimeMonitorDomain::USize32),
            Domain::USize(TargetPointerWidth::W64) => Ok(RuntimeMonitorDomain::USize64),
            Domain::ISize(TargetPointerWidth::W16) => Ok(RuntimeMonitorDomain::ISize16),
            Domain::ISize(TargetPointerWidth::W32) => Ok(RuntimeMonitorDomain::ISize32),
            Domain::ISize(TargetPointerWidth::W64) => Ok(RuntimeMonitorDomain::ISize64),
            Domain::Bool => Ok(RuntimeMonitorDomain::Bool),
        }
    }

    /// The carrier type constant (`Nat` / `UInt64` / `Bool`).
    fn ty(&self) -> Expr {
        match self {
            Domain::RegisteredAdt(carrier) => carrier.ty(),
            Domain::OptionSigned(width) => Expr::app(
                Expr::const_(Name::interned("Option"), vec![Level::zero()]),
                Domain::Signed(*width).ty(),
            ),
            Domain::Nat => nat(),
            Domain::Int => Expr::const_(Name::interned("Int"), vec![]),
            Domain::Machine(width) => Expr::const_(Name::interned(width.carrier()), vec![]),
            Domain::Signed(width) => Expr::app(
                Expr::const_(Name::interned("BitVec"), vec![]),
                Expr::nat_lit(u64::from(width.bits())),
            ),
            Domain::U128 => Expr::app(
                Expr::const_(Name::interned("BitVec"), vec![]),
                Expr::nat_lit(128),
            ),
            Domain::USize(width) | Domain::ISize(width) => Expr::app(
                Expr::const_(Name::interned("BitVec"), vec![]),
                Expr::nat_lit(u64::from(width.bits())),
            ),
            Domain::Bool => Expr::const_(Name::interned("Bool"), vec![]),
        }
    }

    /// The binary op constant name for `+` / `*`. Never called for
    /// [`Domain::Bool`] (arithmetic is gated in `elab_term`); the arm returns an
    /// unresolved sentinel so a missed gate fails as a kernel `UnknownConst`
    /// rather than silently or by panic.
    fn op(&self, which: &str) -> Cow<'static, str> {
        match self {
            Domain::RegisteredAdt(_) => Cow::Borrowed("RegisteredAdt.__no_arithmetic__"),
            Domain::OptionSigned(_) => Cow::Borrowed("Option.__no_arithmetic__"),
            Domain::Nat => match which {
                "add" => Cow::Borrowed("Nat.add"),
                "sub" => Cow::Borrowed("Nat.sub"),
                "mul" => Cow::Borrowed("Nat.mul"),
                "div" => Cow::Borrowed("Nat.div"),
                "mod" => Cow::Borrowed("Nat.mod"),
                _ => Cow::Owned(format!("Nat.{which}")),
            },
            Domain::Int => match which {
                "add" => Cow::Borrowed("Int.add"),
                "sub" => Cow::Borrowed("Int.sub"),
                "mul" => Cow::Borrowed("Int.mul"),
                "div" => Cow::Borrowed("Int.div"),
                "mod" => Cow::Borrowed("Int.mod"),
                _ => Cow::Owned(format!("Int.{which}")),
            },
            Domain::Machine(width) => match (width, which) {
                (MachineUIntWidth::U8, "add") => Cow::Borrowed("UInt8.add"),
                (MachineUIntWidth::U8, "sub") => Cow::Borrowed("UInt8.sub"),
                (MachineUIntWidth::U8, "mul") => Cow::Borrowed("UInt8.mul"),
                (MachineUIntWidth::U16, "add") => Cow::Borrowed("UInt16.add"),
                (MachineUIntWidth::U16, "sub") => Cow::Borrowed("UInt16.sub"),
                (MachineUIntWidth::U16, "mul") => Cow::Borrowed("UInt16.mul"),
                (MachineUIntWidth::U32, "add") => Cow::Borrowed("UInt32.add"),
                (MachineUIntWidth::U32, "sub") => Cow::Borrowed("UInt32.sub"),
                (MachineUIntWidth::U32, "mul") => Cow::Borrowed("UInt32.mul"),
                (MachineUIntWidth::U64, "add") => Cow::Borrowed("UInt64.add"),
                (MachineUIntWidth::U64, "sub") => Cow::Borrowed("UInt64.sub"),
                (MachineUIntWidth::U64, "mul") => Cow::Borrowed("UInt64.mul"),
                _ => Cow::Owned(format!("{}.{which}", width.carrier())),
            },
            Domain::Signed(_) | Domain::U128 | Domain::USize(_) | Domain::ISize(_) => {
                Cow::Owned(format!("BitVec.__use_exact_{which}_encoding__"))
            }
            Domain::Bool => Cow::Borrowed("Bool.__no_arithmetic__"),
        }
    }

    fn arithmetic(&self, which: &str, lhs: Expr, rhs: Expr) -> Result<Expr, String> {
        match self {
            Domain::RegisteredAdt(_) => Err(self.registered_operation_refusal("arithmetic")),
            Domain::OptionSigned(_) => Err(format!(
                "arithmetic is not supported for `{}` (an Option carrier has \
                 constructors and equality only)",
                self.rust_name()
            )),
            // `Int` joins the direct-application arm: `Int.add`/`Int.sub`/
            // `Int.mul` are prelude constants (MEASURED by
            // `tests/nat_lift_probes.rs::pin_int_prelude_constants_present`),
            // and unlike the machine carriers there is no wrap to re-encode.
            // `div`/`mod` reach this arm only behind the literal-divisor gate
            // in `elab_term`, and `Int.div`/`Int.mod` exist there too.
            Domain::Nat | Domain::Int | Domain::Machine(_) => {
                let op = self.op(which);
                Ok(Expr::apps(Expr::const_(Name::interned(&op), vec![]), [lhs, rhs]))
            }
            Domain::Signed(_) | Domain::U128 | Domain::USize(_) | Domain::ISize(_) => {
                let lhs = self.bitvec_to_nat(lhs)?;
                let rhs = self.bitvec_to_nat(rhs)?;
                let nat_value = match which {
                    "add" => Expr::apps(
                        Expr::const_(Name::interned("Nat.add"), vec![]),
                        [lhs, rhs],
                    ),
                    "mul" => Expr::apps(
                        Expr::const_(Name::interned("Nat.mul"), vec![]),
                        [lhs, rhs],
                    ),
                    "sub" => {
                        // `(a + 2^w) - b` is non-negative for in-range a,b and
                        // is congruent to `a-b (mod 2^w)`.  Re-embedding via
                        // `BitVec.ofNat` therefore gives exact wrapping
                        // subtraction without relying on an unseeded BitVec op.
                        let Some(bits) = self.bitvec_bits() else {
                            return Err(format!(
                                "`{}` is not represented by a BitVec",
                                self.rust_name()
                            ));
                        };
                        let modulus = Expr::apps(
                            Expr::const_(Name::interned("Nat.pow"), vec![]),
                            [Expr::nat_lit(2), Expr::nat_lit(u64::from(bits))],
                        );
                        let biased = Expr::apps(
                            Expr::const_(Name::interned("Nat.add"), vec![]),
                            [lhs, modulus],
                        );
                        Expr::apps(
                            Expr::const_(Name::interned("Nat.sub"), vec![]),
                            [biased, rhs],
                        )
                    }
                    _ => {
                        return Err(format!(
                            "arithmetic operation `{which}` is not implemented for `{}`",
                            self.rust_name()
                        ));
                    }
                };
                self.bitvec_of_nat(nat_value)
            }
            Domain::Bool => Err("arithmetic is not supported for `bool`".into()),
        }
    }

    /// Comparison over this domain. Machine-int order IS `toNat` order (the
    /// BitVec carrier's `≤`/`<` are defined by `toNat`), so we compare through
    /// `<Carrier>.toNat` — sound and definitional. `Nat` compares directly.
    /// Never called for [`Domain::Bool`] (ordering is gated in `elaborate_prop`).
    fn cmp(&self, name: &str, a: Expr, b: Expr) -> Expr {
        let nat_cmp = match name {
            "le" => Cow::Borrowed("Nat.le"),
            "lt" => Cow::Borrowed("Nat.lt"),
            _ => Cow::Owned(format!("Nat.{name}")),
        };
        match self {
            Domain::RegisteredAdt(_) => nat_pred("RegisteredAdt.__no_ordering__", a, b),
            Domain::OptionSigned(_) => nat_pred("Option.__no_ordering__", a, b),
            Domain::Nat => nat_pred(&nat_cmp, a, b),
            // `Int.le`/`Int.lt` are present in the pinned prelude — MEASURED,
            // not assumed: the nat-lift design's open risk R-7 said their
            // availability was unknown (they are lazily initialised behind an
            // import-mode switch), and `pin_int_prelude_constants_present` is
            // the measurement that closes it. If a future pin drops them, that
            // test goes red before any goal does.
            Domain::Int => {
                let int_cmp = match name {
                    "le" => Cow::Borrowed("Int.le"),
                    "lt" => Cow::Borrowed("Int.lt"),
                    _ => Cow::Owned(format!("Int.{name}")),
                };
                nat_pred(&int_cmp, a, b)
            }
            Domain::Machine(width) => {
                let to_nat = Expr::const_(Name::interned(width.to_nat_const()), vec![]);
                let an = Expr::app(to_nat.clone(), a);
                let bn = Expr::app(to_nat, b);
                nat_pred(&nat_cmp, an, bn)
            }
            Domain::Signed(_) | Domain::U128 | Domain::USize(_) | Domain::ISize(_) => {
                match (self.bitvec_order_key(a), self.bitvec_order_key(b)) {
                    (Ok(an), Ok(bn)) => nat_pred(&nat_cmp, an, bn),
                    _ => {
                        nat_pred("BitVec.__invalid_ordering__", Expr::nat_lit(0), Expr::nat_lit(0))
                    }
                }
            }
            Domain::Bool => nat_pred("Bool.__no_ordering__", a, b),
        }
    }

    /// Equality over this domain (homogeneous `Eq <ty>`).
    fn eq(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::interned("Eq"), vec![Level::succ(Level::zero())]),
                    self.ty(),
                ),
                lhs,
            ),
            rhs,
        )
    }

    /// The literal `0` in this domain (`Nat.zero` / `<Carrier>.ofNat 0`). Never
    /// called for [`Domain::Bool`] (integer literals are gated in `elab_term`);
    /// the arm returns an unresolved sentinel (see [`Domain::op`]).
    fn zero(&self) -> Expr {
        match self {
            Domain::RegisteredAdt(_) => Expr::const_(Name::interned("RegisteredAdt.__no_zero__"), vec![]),
            Domain::OptionSigned(_) => {
                Expr::const_(Name::interned("Option.__no_zero__"), vec![])
            }
            Domain::Nat => Expr::const_(Name::interned("Nat.zero"), vec![]),
            Domain::Int => Expr::app(
                Expr::const_(Name::interned("Int.ofNat"), vec![]),
                Expr::const_(Name::interned("Nat.zero"), vec![]),
            ),
            Domain::Machine(width) => Expr::app(
                Expr::const_(Name::interned(width.of_nat_const()), vec![]),
                Expr::const_(Name::interned("Nat.zero"), vec![]),
            ),
            Domain::Signed(width) => Expr::apps(
                Expr::const_(Name::interned("BitVec.ofNat"), vec![]),
                [
                    Expr::nat_lit(u64::from(width.bits())),
                    Expr::const_(Name::interned("Nat.zero"), vec![]),
                ],
            ),
            Domain::U128 => Expr::apps(
                Expr::const_(Name::interned("BitVec.ofNat"), vec![]),
                [
                    Expr::nat_lit(128),
                    Expr::const_(Name::interned("Nat.zero"), vec![]),
                ],
            ),
            Domain::USize(width) | Domain::ISize(width) => Expr::apps(
                Expr::const_(Name::interned("BitVec.ofNat"), vec![]),
                [
                    Expr::nat_lit(u64::from(width.bits())),
                    Expr::const_(Name::interned("Nat.zero"), vec![]),
                ],
            ),
            Domain::Bool => Expr::const_(Name::interned("Bool.__no_zero__"), vec![]),
        }
    }

    /// The literal natural number `n` in this domain.
    ///
    /// `Nat` uses the kernel's compact `Nat` literal node — definitionally
    /// `Nat.succ^n Nat.zero`, but a single node rather than `n` successor
    /// applications, so a large bound like `x < 1_000_000` stays a constant-size
    /// term. A machine width uses `<Carrier>.ofNat n`, but ONLY when `n` fits
    /// the width: an out-of-range literal FAILS CLOSED, mirroring Rust's own
    /// "literal out of range for `uN`" rejection, so a spec can never silently
    /// pick up `ofNat`'s wrap-around (`UInt8.ofNat 300 = 44`) — the elaborated
    /// statement always denotes the integer the source spelled.
    ///
    /// The `0` case is left to [`Domain::zero`], which keeps the exact
    /// `Nat.zero` / `ofNat Nat.zero` form the existing certified monitors and
    /// tests were minted against.
    fn numeral(&self, n: u128) -> Result<Expr, String> {
        match self {
            Domain::RegisteredAdt(_) => Err(self.registered_operation_refusal("integer literals")),
            Domain::OptionSigned(_) => Err(format!(
                "an integer literal is not a `{}` (write `Some(<literal>)` or \
                 `None`)",
                self.rust_name()
            )),
            Domain::Nat => Ok(kernel_nat_lit(n)),
            // Unbounded: no range check, by definition. `Int.ofNat` of the
            // compact `Nat` literal keeps the term constant-size, the same
            // property the `Nat` row above relies on.
            Domain::Int => Ok(Expr::app(
                Expr::const_(Name::interned("Int.ofNat"), vec![]),
                kernel_nat_lit(n),
            )),
            Domain::Machine(width) => {
                if n > width.max_value() {
                    return Err(format!(
                        "literal {n} is out of range for `{}` (max {})",
                        width.rust_name(),
                        width.max_value()
                    ));
                }
                Ok(Expr::app(
                    Expr::const_(Name::interned(width.of_nat_const()), vec![]),
                    kernel_nat_lit(n),
                ))
            }
            Domain::Signed(_) | Domain::ISize(_) => {
                let Some(bits) = self.bitvec_bits() else {
                    return Err(format!(
                        "`{}` is not represented by a BitVec",
                        self.rust_name()
                    ));
                };
                if bits < 1 || bits > 128 {
                    return Err(format!(
                        "`{}` has BitVec width {bits}; the width helpers accept 1..=128",
                        self.rust_name()
                    ));
                }
                let max = signed_positive_max(bits);
                if n > max {
                    return Err(format!(
                        "literal {n} is out of range for `{}` (max {max})",
                        self.rust_name()
                    ));
                }
                self.bitvec_of_nat(kernel_nat_lit(n))
            }
            Domain::U128 | Domain::USize(_) => {
                let Some(bits) = self.bitvec_bits() else {
                    return Err(format!(
                        "`{}` is not represented by a BitVec",
                        self.rust_name()
                    ));
                };
                if bits < 1 || bits > 128 {
                    return Err(format!(
                        "`{}` has BitVec width {bits}; the width helpers accept 1..=128",
                        self.rust_name()
                    ));
                }
                let max = bit_mask(bits);
                if n > max {
                    return Err(format!(
                        "literal {n} is out of range for `{}` (max {max})",
                        self.rust_name()
                    ));
                }
                self.bitvec_of_nat(kernel_nat_lit(n))
            }
            Domain::Bool => Err("an integer literal is not a `bool`".into()),
        }
    }

    fn negative_numeral(&self, magnitude: u128) -> Result<Expr, String> {
        // `Int` is unbounded, so `-m` is `Int.negSucc (m - 1)` with no range
        // check and no bit pattern. `-0` is `Int.ofNat 0`, not `negSucc`,
        // because `negSucc k` denotes `-(k+1)` and so has no zero.
        if matches!(self, Domain::Int) {
            if magnitude == 0 {
                return Ok(self.zero());
            }
            return Ok(Expr::app(
                Expr::const_(Name::interned("Int.negSucc"), vec![]),
                kernel_nat_lit(magnitude - 1),
            ));
        }
        if !self.is_signed() {
            return Err(format!("a negative literal is not supported for `{}`", self.rust_name()));
        }
        let Some(bits) = self.bitvec_bits() else {
            return Err(format!(
                "`{}` is not represented by a BitVec",
                self.rust_name()
            ));
        };
        if bits < 1 || bits > 128 {
            return Err(format!(
                "`{}` has BitVec width {bits}; the width helpers accept 1..=128",
                self.rust_name()
            ));
        }
        let max = signed_negative_magnitude_max(bits);
        if magnitude > max {
            return Err(format!(
                "literal -{magnitude} is out of range for `{}` (min -{max})",
                self.rust_name()
            ));
        }
        let pattern = 0u128.wrapping_sub(magnitude) & bit_mask(bits);
        self.bitvec_of_nat(kernel_nat_lit(pattern))
    }

    /// The boolean literal `true`/`false` — only meaningful for [`Domain::Bool`].
    /// Other domains reject a bool literal used as an integer term.
    fn bool_lit(&self, b: bool) -> Result<Expr, String> {
        match self {
            Domain::Bool => Ok(Expr::const_(
                Name::interned(if b { "Bool.true" } else { "Bool.false" }),
                vec![],
            )),
            _ => Err("a `true`/`false` literal is only supported for a `bool` binding".into()),
        }
    }
    /// The number of bits a SHIFT amount must stay below for this carrier, or
    /// `None` for the unbounded `Nat` and the non-numeric `Bool`.
    ///
    /// Folds what used to be `match dom { Domain::Machine(w) => Some(w.bits()),
    /// _ => dom.bitvec_bits() }` into an arm-per-variant form: the wildcard
    /// there answered `None` for `Bool` by accident rather than by decision,
    /// and a future carrier would have inherited that.
    fn shift_width_bits(&self) -> Option<u32> {
        match self {
            Domain::Machine(width) => Some(width.bits()),
            Domain::Signed(width) => Some(width.bits()),
            Domain::U128 => Some(128),
            Domain::USize(width) | Domain::ISize(width) => Some(width.bits()),
            Domain::Nat | Domain::Int | Domain::Bool => None,
            // No shifts on an Option carrier.
            Domain::OptionSigned(_) | Domain::RegisteredAdt(_) => None,
        }
    }

    /// Whether this is the logical [`Domain::Bool`] carrier.
    ///
    /// Written as an EXHAUSTIVE `match` rather than a `matches!`, deliberately:
    /// every site that has to decide "bool or not" routes through here, so
    /// adding a variant to [`Domain`] — the aggregate carrier work is the live
    /// candidate — produces a compile error at the one place that must make
    /// the decision instead of silently defaulting to "not bool".
    fn is_bool(&self) -> bool {
        match self {
            Domain::Bool => true,
            Domain::Nat
            | Domain::Int
            | Domain::Machine(_)
            | Domain::Signed(_)
            | Domain::U128
            | Domain::USize(_)
            | Domain::ISize(_)
            | Domain::OptionSigned(_)
            | Domain::RegisteredAdt(_) => false,
        }
    }

    /// The [`Carrier`] this domain's values inhabit — [`Self::ty`] read as a
    /// COMPARABLE shape rather than a raw kernel `Expr`.
    ///
    /// The two must stay in lockstep: `carrier()` is the normal form of `ty()`,
    /// and every arm below is the same partition of the variants as the arms
    /// there. It is deliberately a `match` per variant, so a new domain has to
    /// name its carrier here rather than inherit one.
    #[must_use]
    pub fn carrier(&self) -> Carrier {
        match self {
            Domain::RegisteredAdt(carrier) => Carrier::RegisteredAdt(carrier.clone()),
            Domain::Nat => Carrier::Nat,
            Domain::Int => Carrier::Int,
            Domain::Machine(width) => Carrier::UInt(*width),
            Domain::Signed(width) => Carrier::BitVec(width.bits()),
            Domain::U128 => Carrier::BitVec(128),
            Domain::USize(width) | Domain::ISize(width) => Carrier::BitVec(width.bits()),
            Domain::Bool => Carrier::Bool,
            Domain::OptionSigned(width) => {
                Carrier::Option(Box::new(Domain::Signed(*width).carrier()))
            }
        }
    }

    /// Whether a value of `self` and a value of `other` are READ alike: one
    /// carrier and one signedness. `Domain -> Carrier` is not injective
    /// (`BitVec 128` is the carrier of `u128` and of `i128`), so equal carriers
    /// alone let a relation read a signed value in unsigned order. The
    /// literal, ordering, division and shift encodings of a `BitVec` domain key
    /// on exactly these two facts, which is why `isize` on a 64-bit target and
    /// `i64` read alike while `u128` and `i128` do not.
    fn reads_like(&self, other: &Domain) -> bool {
        self.carrier() == other.carrier() && self.is_signed() == other.is_signed()
    }

    fn registered_operation_refusal(&self, operation: &str) -> String {
        format!(
            "{operation} has no checked encoding for {}; registered datatypes currently support \
                 exact-carrier bindings, admitted calls and equality. Use a checked model function \
                 for this operation or supply its representation proof before extending the encoding",
            self.carrier().clean_name()
        )
    }

    fn validate_in(&self, env: &Environment) -> Result<(), String> {
        match self {
            Domain::RegisteredAdt(carrier) => carrier.validate_in(env),
            _ => Ok(()),
        }
    }
}

// =====================================================================
// nat-lift (design `scratchpad/designs/design-nat-lift.v2.md`): letting a
// machine-integer Rust clause cite a `Nat`/`Int`-level Lean definition.
//
// THE PROBLEM THIS SOLVES. Every owner Lean model is written over unbounded
// `Nat`/`Int`; a Rust clause atom has ONE machine carrier and its arguments are
// never coerced. So a `u64` function could not apply a `Nat`-carrier definition
// at all ("declares parameter 0 at carrier `Nat`, but the argument is a `u64`
// term ... never coerced"), and "benefit from our Lean definitions" meant
// restating every definition over `UInt64` first.
//
// WHAT IS ADDED. A closed table of EXACT integer injections out of the machine
// carriers, reachable ONLY through the ratified explicit spelling `e as nat` /
// `e as int` (spec surface §12.3), and ONLY in a PROOF-position clause
// elaboration that asked for it ([`ClauseMode::ProofLift`]).
//
// WHAT IS NOT ADDED, and why not.
//   * The IMPLICIT lift — the same injection inserted by the compiler at a
//     `Nat`/`Int`-declared parameter, so the clause reads
//     `ensures result == clamp_nat(c, d)` — needs decision OR-1, because
//     the standing text says an argument is "never coerced" and the implicit
//     form changes what an authored clause MEANS. Until then a machine term at
//     a math position gets [`LiftRefusal::CastRequired`], which prints the cast
//     to write.
//   * Instantiating a `Nat`-quantified cited theorem at lifted arguments, and
//     any compiler-proposed lemma chain, need decision OR-2: they change
//     what a "cited" and an "uncited" row mean. Until then a `Nat`-level
//     theorem cited for a machine-level goal is refused with the one-line
//     wrapper theorem printed.
//   * `usize`/`isize` are refused outright ([`LiftRefusal::PointerWidth`]).
//     Two independent reasons: E9 bindings resolve bare `usize` only through
//     the target-aware entry points, and the compiler mint records an unsigned
//     `PtrSizedInt` as `Machine(U64)` on EVERY target — so a 32-bit target
//     would lift at the wrong width. An untested row in the goal-construction
//     TCB is a bad trade.
//
// SOUNDNESS. Every discharge is still `reject_untyped_goal` followed by a
// kernel check of the proof against the elaborated goal, so a wrong lift
// cannot make a FALSE kernel theorem; it could make a TRUE theorem about a
// proposition the author did not write. That is goal-construction TCB, and
// `docs/TCB.md` names exactly three additions: this table, the
// self-determination rule below, and the mint's recorded return domain for a
// lifted call-headed term (which is why that one is cross-checked twice).
// =====================================================================

/// Which clause fragment one elaboration speaks.
///
/// The mode is an explicit PARAMETER of the public entry points and lives in a
/// thread-local for the duration of a single synchronous elaboration — it is
/// deliberately NOT a field of [`FacetTable`], because one facet table is
/// handed to the body-mint loop as well, and a mode carried by the table would
/// let a Rust BODY be elaborated with lifts in it.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum ClauseMode {
    /// Every public entry point's behaviour before the nat-lift work, to the
    /// byte. `e as nat` is `unsupported term shape` here, exactly as it was.
    #[default]
    Strict,
    /// A PROOF-position user clause: the explicit `as nat` / `as int` lift is
    /// recognized. Nothing else changes; every new branch is reached only
    /// where `Strict` returns an `Err`.
    ProofLift,
}

/// The extra inputs a [`ClauseMode::ProofLift`] elaboration needs, as a struct
/// so that a later increment (the `requires`-as-hypotheses lane) adds a field
/// rather than another positional argument to six call sites.
#[derive(Clone, Debug, Default)]
pub struct ProofClauseInputs {
    mode: ClauseMode,
    /// The Rust spelling of the contracted function's RETURN type, as the
    /// compiler's own type resolution gives it — the SECOND, independent read
    /// of the domain the E6 mint recorded for that function. See
    /// [`TermPin`]'s self-function rule.
    result_ty: Option<String>,
}

impl ProofClauseInputs {
    /// The pre-existing behaviour: no lift, no extra inputs.
    #[must_use]
    pub fn strict() -> Self {
        Self { mode: ClauseMode::Strict, result_ty: None }
    }

    /// A proof-position clause that may carry explicit lifts.
    ///
    /// `result_ty` is the compiler's resolved return-type spelling, or `None`
    /// when the caller has no second read — in which case a lift of a term
    /// headed by the self function fails CLOSED
    /// rather than trusting the mint's single recorded domain.
    #[must_use]
    pub fn proof_lift(result_ty: Option<&str>) -> Self {
        Self { mode: ClauseMode::ProofLift, result_ty: result_ty.map(ToString::to_string) }
    }

    #[must_use]
    pub fn mode(&self) -> ClauseMode {
        self.mode
    }
}

/// The two UNBOUNDED math types a lift may target. Closed on purpose: these
/// are the only codomains in the table, and a `Carrier` outside them is not a
/// lift target at all.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MathTy {
    Nat,
    Int,
}

impl MathTy {
    fn domain(self) -> Domain {
        match self {
            MathTy::Nat => Domain::Nat,
            MathTy::Int => Domain::Int,
        }
    }

    fn spelling(self) -> &'static str {
        match self {
            MathTy::Nat => "nat",
            MathTy::Int => "int",
        }
    }

    /// The math type a spec cast names, or `None` for any other target.
    ///
    /// Read by SPELLING, like every other type name in the clause fragment:
    /// `"nat"`/`"Nat"` is already the ratified clause-fragment spelling of the
    /// unbounded natural domain ([`Domain::from_binding_ty`]), so `as nat`
    /// inherits a reservation that predates this work rather than creating a
    /// new one.
    fn from_syn_type(ty: &syn::Type) -> Option<Self> {
        let syn::Type::Path(p) = ty else { return None };
        if p.qself.is_some() {
            return None;
        }
        let ident = p.path.get_ident()?;
        if ident == "nat" || ident == "Nat" {
            Some(MathTy::Nat)
        } else if ident == "int" || ident == "Int" {
            Some(MathTy::Int)
        } else {
            None
        }
    }
}

/// One EXACT integer injection out of a Rust domain into a math type.
///
/// Every variant is a total, injective, order-preserving map onto the exact
/// integer the Rust value denotes. There is deliberately no variant in the
/// other direction: nothing here ever emits `UIntN.ofNat` or `BitVec.ofNat`,
/// which WRAP (`UInt64.toNat (UInt64.ofNat (2^64)) = 0`, measured in
/// `tests/nat_lift_probes.rs`), so the compiler can never narrow an unbounded
/// value on the author's behalf.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Lift {
    /// Already at the target math type — `(n as nat)` on a `nat` binder.
    Identity,
    /// `UIntN.toNat e` — the underlying `Fin 2^N` value.
    UIntToNat(MachineUIntWidth),
    /// `BitVec.toNat 128 e` — the `u128` row.
    BitVecToNat,
    /// `Int.ofNat (<inner> e)` — every unsigned row's `Int` twin.
    UnsignedToInt(Box<Lift>),
    /// `trust_checked_toInt{N} e` — the EXISTING seeded two's-complement
    /// value model. Reused rather than spelled fresh: the tree already owns
    /// it, the veripb client kernel's own `toIntN` is delta-defeq to it, and
    /// its documented reason not to be `Int.sub` of `ofNat` literals (~2^63
    /// iota steps on a whnf) applies here verbatim.
    SignedToInt(MachineSIntWidth),
    /// `Int.ofNat e` on a term already at `Nat`.
    NatToInt,
}

impl Lift {
    fn wrap(&self, e: Expr) -> Result<Expr, String> {
        Ok(match self {
            Lift::Identity => e,
            Lift::UIntToNat(width) => Expr::app(
                Expr::const_(Name::interned(width.to_nat_const()), vec![]),
                e,
            ),
            Lift::BitVecToNat => Domain::U128.bitvec_to_nat(e)?,
            Lift::UnsignedToInt(inner) => Expr::app(
                Expr::const_(Name::interned("Int.ofNat"), vec![]),
                inner.wrap(e)?,
            ),
            Lift::SignedToInt(width) => Expr::app(
                Expr::const_(Name::interned(width.signed_lift_const()), vec![]),
                e,
            ),
            Lift::NatToInt => {
                Expr::app(Expr::const_(Name::interned("Int.ofNat"), vec![]), e)
            }
        })
    }

    /// The signed width whose seeded model this lift NAMES, if any. The caller
    /// that holds the kernel environment must seed it — and honour
    /// `seed_decl`'s homonym refusal — before the goal is typed or graded.
    fn required_signed_width(&self) -> Option<MachineSIntWidth> {
        match self {
            Lift::SignedToInt(width) => Some(*width),
            Lift::UnsignedToInt(inner) => inner.required_signed_width(),
            Lift::Identity | Lift::UIntToNat(_) | Lift::BitVecToNat | Lift::NatToInt => None,
        }
    }
}

/// Why a requested lift is refused. Each carries the v7/D3 obligation: what was
/// refused, why, and concrete options.
#[derive(Clone, Debug, PartialEq, Eq)]
enum LiftRefusal {
    /// D-1: a signed value has no `Nat`.
    SignedToNat,
    /// D-1 (the math twin): an `Int` term has no `Nat`.
    IntToNat,
    /// D-12: pointer-width integers are out of the table.
    PointerWidth,
    /// D-11 (removed by OR-1): a machine term at a math position with no cast.
    CastRequired,
    /// D-2: the unbounded value would have to be narrowed to the carried
    /// DECLARED machine carrier.
    ///
    /// The declared carrier is a payload rather than a re-derivation because
    /// both call sites naturally hold a MATH domain on both sides of
    /// [`Self::message`]'s `from`/`to` — a message built from those alone reads
    /// "`x as nat` is a `nat` term where a `nat` is declared", which is a
    /// tautology and states neither what was refused nor why. v7/D3 requires
    /// the machine carrier that could not be reached to be named, and the wrap
    /// witness to be at THAT carrier's width rather than a hardcoded 64.
    Narrowing(Carrier),
    /// No lift exists for this domain at all (`bool`, an Option carrier).
    NoLift,
}

impl LiftRefusal {
    /// `what` is how the offending term should be named back to the author.
    fn message(&self, what: &str, from: &Domain, to: MathTy) -> String {
        let to_name = to.spelling();
        match self {
            LiftRefusal::SignedToNat => format!(
                "`{what} as {to_name}`: `{what}` is an `{}`, which can be negative and has no \
                 `Nat` value\n\
                 note: a machine integer is lifted into Lean by its EXACT integer value \
                 (`u64 -> Nat`, `u64 -> Int`, `i64 -> Int`); reading the bit pattern instead \
                 would turn -1 into 18446744073709551615\n\
                 help: options:\n\
                 - state the Lean definition over `Int` and write `{what} as int`;\n\
                 - if the value is never negative, make the Rust parameter unsigned;\n\
                 - keep a `BitVec` definition and relate it to the `Nat` one with a Lean theorem",
                from.rust_name()
            ),
            LiftRefusal::IntToNat => format!(
                "`{what} as nat`: `{what}` is already an `int` term, which can be negative and \
                 has no `Nat` value\n\
                 note: `Int.toNat` is TRUNCATING (it sends every negative value to 0), so the \
                 compiler will not insert it\n\
                 help: options: compare in `int` instead; or state the non-negativity as its \
                 own clause and write the Lean definition over `Int`"
            ),
            LiftRefusal::PointerWidth => format!(
                "`{what} as {to_name}`: `{}` is a pointer-width integer and is not lifted\n\
                 note: the compiler's E6 import records an unsigned pointer-sized integer at a \
                 FIXED 64-bit domain whatever the target, so a lift decided from it would be \
                 wrong on a 32-bit target — the row is withheld rather than measured on one \
                 target and assumed on the others\n\
                 help: options: contract a `u64`/`i64` wrapper and lift that; or keep the \
                 clause at the machine type and state the Lean definition over `UInt64`",
                from.rust_name()
            ),
            LiftRefusal::CastRequired => format!(
                "`{what}` is a `{}` term at a `{to_name}` position, and a clause argument is \
                 never coerced\n\
                 note: the compiler does not insert the lift on your behalf; that would change \
                 what an authored clause means and is owner ruling OR-1, which is not yet given\n\
                 help: write the lift explicitly: `{what} as {to_name}`",
                from.rust_name()
            ),
            LiftRefusal::Narrowing(declared) => {
                let (wrap_fn, wrap_bits) = match declared {
                    Carrier::UInt(width) => (Cow::Borrowed(width.of_nat_const()), width.bits()),
                    Carrier::BitVec(bits) => (Cow::Owned(format!("BitVec.ofNat {bits}")), *bits),
                    _ => (Cow::Borrowed("UInt64.ofNat"), 64),
                };
                format!(
                    "`{what}` is a `{to_name}` term where the declared carrier is `{}`; an \
                     unbounded integer is never narrowed to a machine integer\n\
                     note: `{wrap_fn}` WRAPS modulo 2^{wrap_bits} \
                     (`UInt64.toNat (UInt64.ofNat (2^64)) = 0`), so inserting it could make a \
                     false clause check\n\
                     help: options: restate the Lean declaration over `{to_name}`; lift the \
                     machine side instead, with `<that term> as {to_name}`; or write the \
                     narrowing yourself as a Lean definition, so the wrap is in your text",
                    declared.clean_name()
                )
            }
            LiftRefusal::NoLift => format!(
                "`{what}` is a `{}` term and has no `{to_name}` value\n\
                 note: the lift table covers the INTEGER carriers only\n\
                 help: options: compare it with `==`/`!=` at its own type; or move the \
                 conversion into a Lean definition",
                from.rust_name()
            ),
        }
    }
}

/// THE LIFT TABLE (§3.1). Closed, and exhaustive over [`Domain`] by
/// construction: a new domain must state its row here rather than inherit one.
fn lift_for(from: &Domain, to: MathTy) -> Result<Lift, LiftRefusal> {
    match (from, to) {
        // already there
        (Domain::Nat, MathTy::Nat) | (Domain::Int, MathTy::Int) => Ok(Lift::Identity),
        // Nat -> Int: exact by definition
        (Domain::Nat, MathTy::Int) => Ok(Lift::NatToInt),
        // unsigned machine -> Nat
        (Domain::Machine(width), MathTy::Nat) => Ok(Lift::UIntToNat(*width)),
        (Domain::U128, MathTy::Nat) => Ok(Lift::BitVecToNat),
        // unsigned machine -> Int, through Nat
        (Domain::Machine(width), MathTy::Int) => {
            Ok(Lift::UnsignedToInt(Box::new(Lift::UIntToNat(*width))))
        }
        (Domain::U128, MathTy::Int) => Ok(Lift::UnsignedToInt(Box::new(Lift::BitVecToNat))),
        // signed machine -> Int, through the EXISTING seeded value model
        (Domain::Signed(width), MathTy::Int) => Ok(Lift::SignedToInt(*width)),
        // refusals
        (Domain::Signed(_), MathTy::Nat) => Err(LiftRefusal::SignedToNat),
        (Domain::Int, MathTy::Nat) => Err(LiftRefusal::IntToNat),
        (Domain::USize(_) | Domain::ISize(_), _) => Err(LiftRefusal::PointerWidth),
        (Domain::Bool | Domain::OptionSigned(_) | Domain::RegisteredAdt(_), _) => Err(LiftRefusal::NoLift),
    }
}

/// The domain a term determines BY ITSELF — the self-determination rule
/// (§3.2), which is the single most important soundness property of this work.
///
/// WHY IT EXISTS. [`argument_domain`] has four sources in an authority
/// ranking, and the last two — the domain the call's OTHER arguments determine,
/// and the enclosing atom's domain — are not facts about this term at all.
/// Before the lift they could only ever pick the carrier a literal was typed
/// at, which is harmless. After it they would pick an integer VALUE: `i128` and
/// `u128` share the carrier `BitVec 128`, so taking the signedness of
/// `bv_id(a)` from a sibling argument would read the same bit pattern as `-1`
/// or as `2^128 - 1` and BOTH goals are well-typed — the kernel cannot catch
/// it. So a lift is decided only from the term's own clause variables and the
/// recorded return domains of the calls in it, and a term whose signedness is
/// not self-determined is refused.
#[derive(Clone, Debug, PartialEq, Eq)]
enum TermPin {
    /// The term determines this domain by itself.
    Pinned(Domain),
    /// Nothing in the term names a domain — an integer literal or an
    /// arithmetic expression over literals. Such a term takes the domain of
    /// the position it appears in, which is what it already does today.
    LiteralOnly,
    /// The term's domain is not self-determined; the string says why, for the
    /// D-8 diagnostic.
    Unpinned(String),
}

/// [`TermPin`] for one clause term. `Err` is the pre-existing "mixed domains in
/// one comparison" family of refusals, which this must not swallow.
fn pinned_domain(e: &SynExpr, var_domains: &BTreeMap<String, Domain>) -> Result<TermPin, String> {
    match e {
        SynExpr::Paren(p) => pinned_domain(&p.expr, var_domains),
        // A cast names its own math type; nothing inside it can change that.
        SynExpr::Cast(cast) => Ok(match MathTy::from_syn_type(&cast.ty) {
            Some(target) => TermPin::Pinned(target.domain()),
            None => {
                let target = &cast.ty;
                TermPin::Unpinned(format!(
                    "`as {}` is not a spec cast",
                    quote::quote!(#target)
                ))
            }
        }),
        SynExpr::Lit(_) => Ok(TermPin::LiteralOnly),
        SynExpr::Unary(u) if matches!(u.op, syn::UnOp::Neg(_)) => {
            pinned_domain(&u.expr, var_domains)
        }
        SynExpr::Path(_) | SynExpr::Field(_) => {
            let Some(name) = atom_var_name(e) else {
                return Ok(TermPin::Unpinned("not a clause variable".to_string()));
            };
            Ok(match var_domains.get(&name) {
                Some(d) => TermPin::Pinned(d.clone()),
                None => TermPin::Unpinned(format!("`{name}` is not a bound clause variable")),
            })
        }
        SynExpr::Binary(b) => {
            let l = pinned_domain(&b.left, var_domains)?;
            let r = pinned_domain(&b.right, var_domains)?;
            join_pins(l, r)
        }
        SynExpr::Call(c) => Ok(call_result_pin(c)),
        _ => Ok(TermPin::Unpinned("unsupported term shape".to_string())),
    }
}

/// The [`TermPin`] of one arithmetic node, from its two operands.
fn join_pins(l: TermPin, r: TermPin) -> Result<TermPin, String> {
    Ok(match (l, r) {
        (TermPin::Unpinned(why), _) | (_, TermPin::Unpinned(why)) => TermPin::Unpinned(why),
        (TermPin::LiteralOnly, other) | (other, TermPin::LiteralOnly) => other,
        (TermPin::Pinned(a), TermPin::Pinned(b)) => {
            if a == b {
                TermPin::Pinned(a)
            } else if a.is_math() != b.is_math() {
                // D-3: `Nat` arithmetic does not wrap and machine arithmetic
                // does, so there is no answer to pick.
                return Err(format!(
                    "arithmetic mixes a `{}` term with a `{}` term\n\
                     note: machine arithmetic WRAPS and math arithmetic does not, so the \
                     compiler does not choose one of them for you\n\
                     help: options: lift the machine operand explicitly \
                     (`… + (x as {})`); or move the arithmetic into the Lean definition",
                    a.rust_name(),
                    b.rust_name(),
                    if a.is_math() { a.rust_name() } else { b.rust_name() }
                ));
            } else {
                return Err(format!(
                    "mixed domains in one comparison (`{}` and `{}`) — the operands of a \
                     single comparison must share a type",
                    a.rust_name(),
                    b.rust_name()
                ));
            }
        }
    })
}

/// The [`TermPin`] of a CALL, read from the ADMISSION's recorded return domain
/// and never from the call's argument variables (§3.4's precedence rule, which
/// is what makes the `(Math, Math)` relation row possible at all).
///
/// The two guards below are the other half of the self-determination rule.
/// After this work `return_domain` selects an integer VALUE rather than just a
/// literal range, so it needs a SECOND independent read before a lift is built
/// on it:
///
///   * the SELF function (the call `result` was rewritten to) is cross-checked
///     against the compiler's own resolved return-type spelling — two
///     independently derived values (HIR/typeck `Ty` versus the extracted
///     `trust_types::Ty`), the same two-read discipline the parameter-list
///     agreement check already uses;
///   * any OTHER call may head a lifted term only when its recorded domain is
///     the UNIQUE preimage of its carrier. A `BitVec N` codomain has three
///     preimages (`iN`, `usize`, `isize` at that width) and answers
///     `Unpinned`.
///
///     BE EXACT ABOUT WHERE THE SECOND READ IS (corrected 2026-09-17: this
///     paragraph used to claim the constant's kernel type "is itself the
///     independent second read", and the code performs no such read — it tests
///     `domain.carrier().unique_domain() == Some(domain)`, a property of the
///     recorded domain alone). The real second read happens downstream:
///     `reject_untyped_goal`/`check_type` rejects `UIntN.toNat` applied to a
///     constant of another type. That is sound here precisely BECAUSE the
///     carriers where kernel typing could not discriminate — the `BitVec`-
///     carried domains, which share one kernel type across several Rust
///     preimages — are exactly the ones `unique_domain` excludes. A future TCB
///     auditor should look for the check there, not here.
fn call_result_pin(c: &syn::ExprCall) -> TermPin {
    let callee = callee_path(c);
    let Some(admission) = ambient_admission(&callee) else {
        return TermPin::Unpinned(format!("`{callee}` is not an admitted spec call"));
    };
    let Some(domain) = admission.return_domain().cloned() else {
        return TermPin::Unpinned(format!(
            "`{callee}` has no recorded result domain (its declared codomain is not one of \
             the closed carriers the clause fragment reads back)"
        ));
    };
    let lift_ctx = ambient_proof_lift();
    if let Some(ctx) = lift_ctx.as_ref().filter(|ctx| ctx.self_fn_name.as_deref() == Some(callee.as_str())) {
        // SELF: the two-read cross-check.
        let Some(spelling) = ctx.result_ty.as_deref() else {
            return TermPin::Unpinned(format!(
                "the compiler supplied no resolved return type for `{callee}`, so the domain \
                 the E6 import recorded has no second, independent read"
            ));
        };
        match Domain::from_binding_ty(spelling) {
            Some(resolved) if resolved == domain => TermPin::Pinned(domain),
            other => TermPin::Unpinned(format!(
                "the two reads of `{callee}`'s return type disagree: the compiler resolved it \
                 as `{spelling}` ({}), while the E6 import recorded `{}`",
                other.map_or_else(
                    || "which the clause fragment does not map to a domain".to_string(),
                    |d| format!("domain `{}`", d.rust_name())
                ),
                domain.rust_name()
            )),
        }
    } else if domain.carrier().unique_domain().as_ref() == Some(&domain) {
        TermPin::Pinned(domain)
    } else {
        TermPin::Unpinned(format!(
            "`{callee}` returns `{}`, whose carrier `{}` has more than one Rust preimage, so \
             its integer value is not determined",
            domain.rust_name(),
            domain.carrier().clean_name()
        ))
    }
}

/// D-8: the term's domain is not self-determined.
fn unpinned_lift_error(what: &str, to: MathTy, why: &str) -> String {
    format!(
        "`{what} as {}`: {why}\n\
         note: `i128` and `u128` share the carrier `BitVec 128`, so a signedness taken from \
         another argument or from the surrounding comparison would decide a VALUE the author \
         never wrote; the compiler therefore never borrows one\n\
         help: options:\n\
         - make the Lean definition return `Nat`/`Int` itself;\n\
         - wrap it in a Lean definition that does \
         (`def f_int (v : BitVec 128) : Int := …`);\n\
         - lift BEFORE the call: pass `x as int` to an `Int`-typed definition",
        to.spelling()
    )
}

/// D-9: `e as T` where `T` is not a spec cast target.
fn non_spec_cast_error(target: &str) -> String {
    format!(
        "`as {target}` is not a spec cast: only `as nat` and `as int` are\n\
         note: a machine-to-machine cast is not in the clause fragment — it would have to \
         choose between wrapping and refusing, and the clause fragment does neither silently\n\
         help: options: lift both sides and compare in `nat`/`int`; or move the conversion \
         into a Lean definition, where its text states what it does"
    )
}

/// Whether an expression tree contains a `Cast` node anywhere.
///
/// This is the gate on the new RELATION path ([`elab_math_relation`]) and on
/// the cast arm itself: `Cast` is `unsupported term shape` in the pre-existing
/// elaborator, so an atom containing one is an atom that fails today.
///
/// IT IS NOT, however, the gate on every new branch, and §5.5's original
/// "true by construction" claim was FALSE as written (measured 2026-09-17,
/// integration review). Two ProofLift-mode changes fire on an atom with no cast
/// anywhere, both inside `elab_term`'s call arm:
///
/// 1. the LITERAL-ARGUMENT row — a literal argument takes the declared
///    parameter's unique preimage instead of the sibling/ambient domain. This
///    is error → success only: the pre-existing rule ACCEPTED an argument only
///    when `arg_dom.carrier() == declared`, and a carrier with a unique
///    preimage has exactly one domain with that carrier, so wherever the old
///    rule succeeded the two pick the same domain. Pinned by
///    `the_uncast_literal_row_is_a_real_mode_difference_and_only_widens`;
/// 2. `pinned_domain(arg)?` is evaluated for every argument, so the D-3
///    "mixed domains in one comparison" refusal can replace a message the
///    pre-existing path produced further downstream. Error → error, different
///    text.
///
/// What holds by construction is the weaker, still useful statement: no atom
/// that elaborates SUCCESSFULLY today elaborates to a different goal in
/// ProofLift mode. That is what
/// [`the_mode_change_is_byte_identical_on_the_uncast_corpus`] measures, on the
/// clause corpus rather than by inspection.
///
/// [`the_mode_change_is_byte_identical_on_the_uncast_corpus`]: #
fn contains_cast(e: &SynExpr) -> bool {
    match e {
        SynExpr::Cast(_) => true,
        SynExpr::Paren(p) => contains_cast(&p.expr),
        SynExpr::Unary(u) => contains_cast(&u.expr),
        SynExpr::Binary(b) => contains_cast(&b.left) || contains_cast(&b.right),
        SynExpr::Call(c) => c.args.iter().any(contains_cast),
        SynExpr::MethodCall(m) => {
            contains_cast(&m.receiver) || m.args.iter().any(contains_cast)
        }
        SynExpr::Field(f) => contains_cast(&f.base),
        _ => false,
    }
}

/// Trust (d1/B2, 2026-09-28): the refusal for a call argument that carries a
/// cast, at [`ClauseMode::Strict`].
///
/// The head is the pre-existing `unsupported term shape` — the message every
/// cast has always had in this mode, and the one
/// `strict_mode_still_refuses_a_cast_with_the_pre_existing_message` pins — so
/// no consumer keyed on it changes. What it replaces is the call-argument
/// path's carrier check, which read `x as nat` as the bare `x` (`argument_domain`
/// resolves through `collect_vars`, which looks through a cast) and so told the
/// author "the argument is a `u16` term" about an argument they had written as
/// a lift. The d1 fallback no longer reaches this mode for an `ensures`
/// citation; every remaining Strict consumer (monitors, `requires`/`invariant`
/// citations, statement-only rows) still can, which is why the message names
/// the position rather than the lift's absence in general.
fn strict_mode_cast_argument_refusal(callee: &str, index: usize, arg: &SynExpr) -> String {
    let src = quote::quote!(#arg).to_string();
    format!(
        "unsupported term shape: argument {index} of `{callee}`, `{src}`, contains a cast; the \
         explicit lift (`e as nat` / `e as int`, spec surface §12.3) is read only where an \
         `ensures` clause is elaborated for proof, and this clause position is elaborated \
         without it, so the cast is refused here rather than read as its operand"
    )
}

/// Elaborate a comparison ATOM that carries at least one lift (§3.4).
///
/// Returns `Ok(None)` when the atom has no cast in it, in which case the caller
/// runs the pre-existing path unchanged. When it does carry one, each SIDE is
/// classified independently and elaborated at ITS OWN domain, and the relation
/// is built at the math type — which is the whole point: the pre-existing
/// `atom_domain` resolves over every free variable INCLUDING a typed call's
/// arguments, so on `clamp_nat(c as nat, d as nat) <= (d as nat)` it would pick
/// `u32` from the variables and build the ill-typed
/// `Nat.le (UInt32.toNat (clamp_nat …)) …`.
fn elab_math_relation(
    b: &syn::ExprBinary,
    vars: &[String],
    offset: u32,
    var_domains: &BTreeMap<String, Domain>,
) -> Result<Option<Expr>, String> {
    if !has_ambient_proof_lift() || !(contains_cast(&b.left) || contains_cast(&b.right)) {
        return Ok(None);
    }
    let left = pinned_domain(&b.left, var_domains)?;
    let right = pinned_domain(&b.right, var_domains)?;
    let math_of = |p: &TermPin| match p {
        TermPin::Pinned(d) if d.is_math() => Some(d.clone()),
        _ => None,
    };
    match (math_of(&left), math_of(&right)) {
        (Some(lm), _) => {
            elab_math_relation_with(b, vars, offset, var_domains, &right, lm, false).map(Some)
        }
        (None, Some(rm)) => {
            elab_math_relation_with(b, vars, offset, var_domains, &left, rm, true).map(Some)
        }
        // Neither side is math: the cast sits somewhere the side classification
        // does not reach (it will be reported by `elab_term` itself), and the
        // pre-existing path owns the atom.
        (None, None) => Ok(None),
    }
}

/// One side is math (`math_dom`); decide the other side and build the relation.
/// `swapped` says the math side is the RIGHT one, so the operands are put back
/// in source order before the relation is built.
fn elab_math_relation_with(
    b: &syn::ExprBinary,
    vars: &[String],
    offset: u32,
    var_domains: &BTreeMap<String, Domain>,
    other_pin: &TermPin,
    math_dom: Domain,
    swapped: bool,
) -> Result<Expr, String> {
    let (math_expr, other_expr) =
        if swapped { (&*b.right, &*b.left) } else { (&*b.left, &*b.right) };
    // The domain each side is BUILT at, and (for a `Nat` side facing an `Int`
    // side) whether it must additionally be embedded.
    let (other_dom, embed_other, relation_dom) = match other_pin {
        TermPin::Pinned(d) if d.is_math() => {
            if *d == math_dom {
                (d.clone(), false, math_dom.clone())
            } else {
                // `Nat` beside `Int`: embed the `Nat` side, compare at `Int`.
                match (&math_dom, d) {
                    (Domain::Int, Domain::Nat) => (Domain::Nat, true, Domain::Int),
                    (Domain::Nat, Domain::Int) => {
                        // the MATH side is the `Nat` one — handled by rebuilding
                        // below, so express it the same way.
                        (Domain::Int, false, Domain::Int)
                    }
                    _ => (d.clone(), false, math_dom.clone()),
                }
            }
        }
        TermPin::LiteralOnly => (math_dom.clone(), false, math_dom.clone()),
        TermPin::Pinned(d) => {
            // A machine term at a math position. Refused — but WHICH refusal
            // depends on whether the cast this would ask for is one the table
            // has. Consulting `lift_for` first is not cosmetic: an unconditional
            // D-11 tells the author of `(x as nat) == y` with `y: i64` to
            // "write `y as nat`", advice that then fails with D-1 — whose whole
            // point is that reading the bit pattern would turn `-1` into
            // `2^64 - 1`. `bool` and the statement-only pointer-sized spellings
            // are the same story. The CALL-argument path has always consulted
            // the table here; this is the relation path catching up.
            let other_src = quote::quote!(#other_expr).to_string();
            let to = if math_dom == Domain::Int { MathTy::Int } else { MathTy::Nat };
            return Err(match lift_for(d, to) {
                Ok(_) => LiftRefusal::CastRequired.message(&other_src, d, to),
                Err(refusal) => refusal.message(&other_src, d, to),
            });
        }
        TermPin::Unpinned(why) => {
            let other_src = quote::quote!(#other_expr).to_string();
            return Err(unpinned_lift_error(
                &other_src,
                if math_dom == Domain::Int { MathTy::Int } else { MathTy::Nat },
                why,
            ));
        }
    };
    // Build each side at its own domain, then embed the `Nat` one if the
    // relation is at `Int`.
    let embed = |e: Expr| Expr::app(Expr::const_(Name::interned("Int.ofNat"), vec![]), e);
    let mut math_side = elab_term(math_expr, vars, offset, var_domains, &math_dom)?;
    let mut other_side = elab_term(other_expr, vars, offset, var_domains, &other_dom)?;
    if relation_dom == Domain::Int {
        if math_dom == Domain::Nat {
            math_side = embed(math_side);
        }
        if embed_other {
            other_side = embed(other_side);
        }
    }
    let (l, r) = if swapped { (other_side, math_side) } else { (math_side, other_side) };
    Ok(match b.op {
        BinOp::Eq(_) => relation_dom.eq(l, r),
        BinOp::Le(_) => relation_dom.cmp("le", l, r),
        BinOp::Lt(_) => relation_dom.cmp("lt", l, r),
        BinOp::Ge(_) => relation_dom.cmp("le", r, l),
        BinOp::Gt(_) => relation_dom.cmp("lt", r, l),
        _ => return Err("comparison op must be one of == != <= < >= >".into()),
    })
}

/// The ambient [`ClauseMode::ProofLift`] context of the current elaboration.
///
/// `None` is [`ClauseMode::Strict`] — the default, and the value every
/// pre-existing public entry point installs. It is a thread-local for the same
/// reason [`ADMISSION_FACETS`] is: it is genuinely ambient context for one
/// synchronous elaboration, and threading it through ~40 recursion sites would
/// add no expressiveness.
#[derive(Clone, Debug, Default)]
struct ProofLiftContext {
    /// The contracted function, when `result` was rewritten to a call on it.
    self_fn_name: Option<String>,
    /// The compiler's own resolved spelling of that function's return type.
    result_ty: Option<String>,
}

thread_local! {
    static PROOF_LIFT: std::cell::RefCell<Option<ProofLiftContext>> =
        const { std::cell::RefCell::new(None) };
}

/// RAII guard installing the proof-lift context, restoring the previous value
/// on drop so a nested elaboration cannot leak its mode to an outer one and a
/// panic mid-elaboration cannot leave a stale one behind.
struct ProofLiftScope {
    previous: Option<ProofLiftContext>,
}

impl ProofLiftScope {
    fn enter(inputs: &ProofClauseInputs, self_fn_name: Option<&str>) -> Self {
        let next = match inputs.mode {
            ClauseMode::Strict => None,
            ClauseMode::ProofLift => Some(ProofLiftContext {
                self_fn_name: self_fn_name.map(ToString::to_string),
                result_ty: inputs.result_ty.clone(),
            }),
        };
        ProofLiftScope { previous: PROOF_LIFT.with(|slot| slot.replace(next)) }
    }
}

impl Drop for ProofLiftScope {
    fn drop(&mut self) {
        PROOF_LIFT.with(|slot| *slot.borrow_mut() = self.previous.take());
    }
}

fn ambient_proof_lift() -> Option<ProofLiftContext> {
    PROOF_LIFT.with(|slot| slot.borrow().clone())
}

fn has_ambient_proof_lift() -> bool {
    PROOF_LIFT.with(|slot| slot.borrow().is_some())
}

// Trust (ref-self I1): the SELF-CALL key of the current elaboration — the exact
// spelling `elaborate_ensures` splices in for `result`.
//
// It is a SECOND thread-local rather than a field of [`ProofLiftContext`]
// because that context exists only at `ClauseMode::ProofLift`, while the
// self-result-only gate must hold in every mode. Every entry point that does
// NOT know a self spelling installs `None`, and a `self_result_only` admission
// is then unnameable — the fail-closed direction.
thread_local! {
    static SELF_FN_KEY: std::cell::RefCell<Option<String>> =
        const { std::cell::RefCell::new(None) };
}

/// RAII guard installing the self-call key, restoring the previous value on
/// drop (same discipline as [`ProofLiftScope`]).
struct SelfFnScope {
    previous: Option<String>,
}

impl SelfFnScope {
    fn enter(self_fn_name: Option<&str>) -> Self {
        let next = self_fn_name.map(ToString::to_string);
        SelfFnScope { previous: SELF_FN_KEY.with(|slot| slot.replace(next)) }
    }
}

impl Drop for SelfFnScope {
    fn drop(&mut self) {
        SELF_FN_KEY.with(|slot| *slot.borrow_mut() = self.previous.take());
    }
}

fn is_ambient_self_fn_key(candidate: &str) -> bool {
    SELF_FN_KEY.with(|slot| slot.borrow().as_deref() == Some(candidate))
}

/// Trust (ref-self I1): the ONE refusal a view import carries, shared by the
/// call and the bare position so the two cannot drift (v7/D3: rule, why THIS
/// program broke it, options).
fn view_import_unnameable_refusal(name: &str, admission: &Admission) -> String {
    format!(
        "`{name}` is E6-admitted only through a borrow-erased PARAMETER VIEW (`{view}`), whose \
         kernel import takes the pointee's scalar fields as separate arguments — so it is not \
         nameable in a clause, where `{name}` would name the Rust signature instead. It denotes \
         only `result` in `{name}`'s own `ensures`. options: (1) name the field values directly \
         (`{name}`'s own clause may write `self.x`); (2) write a by-value helper taking the \
         scalars and call THAT; (3) keep this clause solver-only",
        view = admission.view().unwrap_or(""),
    )
}

// The signed lift widths the most recent elaboration NAMED, accumulated while
// the goal is built.
//
// The elaborator holds no kernel environment, so it cannot seed
// `trust_checked_toInt{N}` itself. It records which widths the goal names, and
// the caller that DOES hold the environment must seed each one — and honour
// `seed_decl`'s refusal of a foreign homonym — before the goal is typed or
// graded. That is the second of the two independent checks against an island
// capturing the lift constant's name; the first is the reserved
// `trust_checked_` prefix on the island side.
thread_local! {
    static REQUIRED_SIGNED_LIFTS: std::cell::RefCell<Vec<MachineSIntWidth>> =
        const { std::cell::RefCell::new(Vec::new()) };
}

fn record_required_signed_lift(lift: &Lift) {
    if let Some(width) = lift.required_signed_width() {
        REQUIRED_SIGNED_LIFTS.with(|slot| {
            let mut slot = slot.borrow_mut();
            if !slot.contains(&width) {
                slot.push(width);
            }
        });
    }
}

fn take_required_signed_lifts() -> Vec<MachineSIntWidth> {
    REQUIRED_SIGNED_LIFTS.with(|slot| std::mem::take(&mut *slot.borrow_mut()))
}

/// A clause goal plus the environment obligations its construction created.
#[derive(Clone, Debug)]
pub struct ElaboratedClause {
    /// The kernel proposition.
    pub goal: Expr,
    /// Signed widths whose seeded lift model (`trust_checked_toInt{N}`) the
    /// goal NAMES. The holder of the kernel environment must
    /// [`seed_signed_lift_model`] each of these — which fails closed on a
    /// foreign homonym — BEFORE typing or grading the goal.
    pub required_signed_lift_widths: Vec<MachineSIntWidth>,
}

/// Collect free variable identifiers in order of first appearance.
fn collect_vars(e: &SynExpr, out: &mut Vec<String>) {
    match e {
        SynExpr::Paren(p) => collect_vars(&p.expr, out),
        // A spec cast is transparent to the FREE-VARIABLE gate: `result as nat`
        // still mentions `result`, and `(x as nat) <= n` still mentions `x`.
        // Without this arm the exact-binding gate would see no occurrence and
        // the variable would be silently ∀-closed — fail-closed, but as a
        // generally false goal rather than a named refusal.
        SynExpr::Cast(cast) => collect_vars(&cast.expr, out),
        SynExpr::Binary(b) => {
            collect_vars(&b.left, out);
            collect_vars(&b.right, out);
        }
        SynExpr::Unary(u) => collect_vars(&u.expr, out),
        SynExpr::Path(p) => {
            if let Some(id) = p.path.get_ident() {
                // `None` is the Option constructor LITERAL, never a clause
                // variable: Rust itself refuses a binding named `None`
                // (E0530, unit-variant shadowing), so no parameter row can
                // ever exist for it — collecting it would only poison the
                // exact-binding gate with a bogus free variable.
                if id != "None" && !out.iter().any(|existing| id == existing.as_str()) {
                    out.push(id.to_string());
                }
            }
        }
        // A depth-1 named field projection is ONE opaque scalar variable named
        // by its dotted path (`c.degree`). A richer field shape collects
        // NOTHING here — and is refused by name in `elab_term`, which is the
        // only place a term is ever built, so an uncollected projection can
        // never reach the kernel as a variable-free atom.
        SynExpr::Field(_) => {
            if let Some(name) = atom_var_name(e) {
                if !out.contains(&name) {
                    out.push(name);
                }
            }
        }
        // E6 (two-language design §3.1): a variable occurring ONLY inside a
        // call argument is still a free variable of the clause, so the domain
        // gate must see it. Visit the arguments — but NOT the callee path
        // (`c.func`) / method name: those are function identities, not
        // clause variables, and collecting them would poison domain
        // resolution with a bogus binding. The call itself still fails closed
        // in production: public E6 facet findings are diagnostic only, and no
        // sealed, item-bound kernel-import admission exists. This walk only
        // keeps the free-variable set complete for that diagnostic and for a
        // future authority-bearing importer.
        SynExpr::Call(c) => {
            for arg in &c.args {
                collect_vars(arg, out);
            }
        }
        SynExpr::MethodCall(m) => {
            collect_vars(&m.receiver, out);
            for arg in &m.args {
                collect_vars(arg, out);
            }
        }
        _ => {}
    }
}

/// Select the exact typed bindings that occur free in one clause from a
/// caller-provided complete function signature.
///
/// The returned vector follows first source occurrence and contains no extra
/// bindings, so it is suitable for [`elaborate_goal_typed`]'s exact-bijection
/// gate. Missing names, duplicate available names, and malformed clauses fail
/// closed. Type strings are deliberately left uninterpreted here; the typed
/// elaborator remains the single authority for supported carriers and mixed
/// domains. This helper only narrows a structural input table and confers no
/// statement or VC authority.
pub fn exact_typed_bindings_for_clause(
    spec: &str,
    available_types: &[(&str, &str)],
) -> Result<Vec<(String, String)>, String> {
    // Use the same conservative clause parser as typed elaboration so a
    // head-level quantifier can bind its own variable without forcing that
    // name into the function-signature table. This remains a statement-only
    // selector: it mints no function admission or verification verdict.
    let clause = parse_qclause(spec, true)?;
    let mut vars = Vec::new();
    collect_qclause_free_vars(&clause, &mut Vec::new(), &mut vars);
    let mut binders = Vec::new();
    collect_qclause_binders(&clause, &mut binders);

    let mut available = BTreeMap::new();
    for &(name, ty) in available_types {
        if name.is_empty() {
            return Err("clause variable binding has an empty name".to_string());
        }
        if available.insert(name, ty).is_some() {
            return Err(format!("duplicate clause variable binding `{name}`"));
        }
    }
    for binder in binders {
        if available.contains_key(binder.as_str()) {
            return Err(format!(
                "quantifier binder `{binder}` shadows a function-signature binding"
            ));
        }
    }

    vars.into_iter()
        .map(|name| {
            available
                .get(name.as_str())
                .map(|ty| (name.clone(), (*ty).to_string()))
                .ok_or_else(|| format!("missing supported type for clause variable `{name}`"))
        })
        .collect()
}

/// A positive integer literal `n >= 1`, seeing through parentheses. Used to
/// admit `/` and `%` ONLY by a statically-nonzero divisor — the sole shape for
/// which the executable monitor cannot divide by zero at runtime and the
/// kernel's total `div`/`mod` (which define `x / 0 = 0`) agree with Rust's
/// trapping division for every input.
fn positive_int_literal(e: &SynExpr) -> Option<u128> {
    match e {
        SynExpr::Paren(p) => positive_int_literal(&p.expr),
        SynExpr::Lit(l) => match &l.lit {
            Lit::Int(i) => i.base10_parse::<u128>().ok().filter(|&n| n >= 1),
            _ => None,
        },
        _ => None,
    }
}

/// A non-negative integer literal `n >= 0`, seeing through parentheses. Used for
/// a bit-SHIFT amount (`x << n`), which must be a literal so `2^n` is known at
/// elaboration; `0` is a valid (identity) shift.
fn nonneg_int_literal(e: &SynExpr) -> Option<u128> {
    match e {
        SynExpr::Paren(p) => nonneg_int_literal(&p.expr),
        SynExpr::Lit(l) => match &l.lit {
            Lit::Int(i) => i.base10_parse::<u128>().ok(),
            _ => None,
        },
        _ => None,
    }
}

/// Desugar `a != b` into `!(a == b)` at the syntax level. Every downstream
/// path — the kernel proposition, the monitor decision, and the executable
/// twin — then realizes `!=` through the existing `Not`/`Eq` machinery, so the
/// three stay consistent by construction (no separate disequality certificate
/// to keep in step) and `!=` inherits the equality lane's exact domain
/// semantics.
fn ne_as_not_eq(b: &syn::ExprBinary) -> SynExpr {
    let eq = SynExpr::Binary(syn::ExprBinary {
        attrs: Vec::new(),
        left: b.left.clone(),
        op: BinOp::Eq(syn::token::EqEq::default()),
        right: b.right.clone(),
    });
    SynExpr::Unary(syn::ExprUnary {
        attrs: Vec::new(),
        op: syn::UnOp::Not(syn::token::Not::default()),
        expr: Box::new(eq),
    })
}

/// The de Bruijn index of the variable at `pos` among `vars_len` binders in
/// outer-to-inner order (the last binder is index 0), `offset` binders deeper.
///
/// Callers obtain `pos` from `Iterator::position` over `vars` or an explicitly
/// range-checked select parameter, so `pos < vars_len` holds — but the verifier
/// sees `position`'s result as opaque and refuted `vars.len() - 1 - pos` at
/// `pos = vars.len()`, and
/// the final `+ offset` at `offset = u32::MAX` (measured 2026-09-13 on
/// `dff2b22d1`). Both are stated here as refusals: the first can only be an
/// internal error, the second a clause nested deeper than the kernel's `u32`
/// index space can name.
fn de_bruijn_index(vars_len: usize, pos: usize, offset: u32) -> Result<u32, String> {
    if pos >= vars_len {
        return Err(format!(
            "internal error: binder position {pos} is outside the {vars_len} binders in scope"
        ));
    }
    let depth = vars_len - 1 - pos;
    let depth = u32::try_from(depth)
        .map_err(|_| format!("binder depth {depth} exceeds the kernel's `u32` de Bruijn index"))?;
    depth.checked_add(offset).ok_or_else(|| {
        format!("binder depth {depth} + {offset} exceeds the kernel's `u32` de Bruijn index")
    })
}

/// `offset + 1`: the binder depth one arrow (or one binder) deeper. Fails
/// closed instead of overflowing at `u32::MAX` — a clause nested 2^32 deep is
/// not something the kernel's `u32` de Bruijn index can name, and the
/// verifier refuted the bare `offset + 1` there (measured 2026-09-13 on
/// `dff2b22d1`).
fn one_binder_deeper(offset: u32) -> Result<u32, String> {
    offset
        .checked_add(1)
        .ok_or_else(|| "binder depth exceeds the kernel's `u32` de Bruijn index".to_string())
}

/// Elaborate a term. `vars` is the outer-to-inner binder order; a variable at
/// position `i` has de Bruijn index `vars.len() - 1 - i` **plus `offset`** —
/// where `offset` counts binders introduced *between* the ∀-vars and this term
/// (e.g. the precondition arrow in a `requires ⇒ ensures` contract).
fn elab_term(
    e: &SynExpr,
    vars: &[String],
    offset: u32,
    var_domains: &BTreeMap<String, Domain>,
    dom: &Domain,
) -> Result<Expr, String> {
    match e {
        SynExpr::Paren(p) => elab_term(&p.expr, vars, offset, var_domains, dom),
        SynExpr::Path(p) => {
            let ident = p
                .path
                .get_ident()
                .ok_or_else(|| "only bare identifiers are supported".to_string())?;
            // `None` is the Option CONSTRUCTOR literal, never a clause
            // variable (Rust refuses a binding named `None` — E0530), typed
            // exactly at an Option carrier: `Option.none.{0} (BitVec N)`.
            if ident == "None" {
                if let Domain::OptionSigned(width) = dom {
                    return Ok(Expr::app(
                        Expr::const_(Name::interned("Option.none"), vec![Level::zero()]),
                        Domain::Signed(*width).ty(),
                    ));
                }
                return Err(format!(
                    "`None` is an Option constructor and needs an Option-carrier position \
                     (here the operand carrier is `{}`); it can appear only against an \
                     admitted checked-arithmetic result",
                    dom.rust_name()
                ));
            }
            if let Some(pos) = vars.iter().position(|v| ident == v.as_str()) {
                return Ok(Expr::bvar(de_bruijn_index(vars.len(), pos, offset)?));
            }
            let id = ident.to_string();
            // E6 bare citation (e6 probe f04's spelling): an admitted
            // ZERO-ARITY constant referenced with NO argument list elaborates
            // to its kernel constant — the same admission, the same I3
            // firewall, and the same constant the call arm resolves for
            // `id()`; only the surface spelling differs. A parametered
            // admission must be applied: its bare name is a function value,
            // which the term fragment does not speak, so it keeps failing
            // closed — with the fix named (v7/D3).
            //
            // I0: the goal binder above wins FIRST, and this consult refuses
            // outright when the compiler recorded a Rust binding of this name
            // that produced no binder (a by-value struct parameter, a `&T`).
            if let Some(admission) = ambient_bare_admission(&id)? {
                // I3: capability decided before arity, same as the call arm.
                if let Err(refusal) = admission.require_at(ambient_use_site(), &id) {
                    return Err(refusal.to_string());
                }
                if admission.arity != 0 {
                    return Err(format!(
                        "admitted `{id}` has arity {} and must be applied \
                         (`{id}(…)`); a bare reference to a parametered \
                         definition is outside the term fragment",
                        admission.arity
                    ));
                }
                return Ok(Expr::const_(Name::from_string(&admission.kernel_const), vec![]));
            }
            Err(format!("unbound variable `{id}`"))
        }
        // A DOTTED PATH is one opaque scalar atom (see [`atom_var_name`]): it
        // resolves to the binder the compiler declared for `p.field`, with the
        // field's own carrier, and the aggregate itself never appears. Any
        // richer field shape is refused HERE, by name — this is the only place
        // a projection can become a term, so the refusal is total.
        SynExpr::Field(_) => {
            let id = atom_var_name(e).ok_or_else(|| {
                "only a depth-1 named field projection of a parameter (`p.field`) is supported \
                 in a clause; a nested projection, a tuple index, or a projection off a \
                 non-identifier needs the aggregate carrier and fails closed"
                    .to_string()
            })?;
            let pos = vars
                .iter()
                .position(|v| *v == id)
                .ok_or_else(|| format!("unbound variable `{id}`"))?;
            Ok(Expr::bvar(de_bruijn_index(vars.len(), pos, offset)?))
        }
        SynExpr::Lit(l) => match &l.lit {
            Lit::Int(i) => {
                if matches!(dom, Domain::RegisteredAdt(_)) {
                    return Err(dom.registered_operation_refusal("integer literals"));
                }
                if !i.suffix().is_empty() && Domain::from_binding_ty(i.suffix()).as_ref() != Some(dom) {
                    return Err(format!("literal suffix `{}` disagrees with the operand carrier `{}`; \
                        use a matching literal type or an explicit checked conversion", i.suffix(), dom.rust_name()));
                }
                let n: u128 = i.base10_parse().map_err(|e| format!("bad int: {e}"))?;
                if n == 0 {
                    Ok(dom.zero())
                } else {
                    // A non-negative literal `n` — the domain's compact numeral,
                    // range-checked for machine widths (see `Domain::numeral`).
                    dom.numeral(n)
                }
            }
            // `true`/`false` as a term — only in a `bool` clause (e.g. the RHS of
            // `flag == true`); `Domain::bool_lit` rejects it for other domains.
            Lit::Bool(b) => dom.bool_lit(b.value),
            _ => Err("unsupported literal (integer or `true`/`false` only)".into()),
        },
        SynExpr::Unary(u) if matches!(u.op, syn::UnOp::Neg(_)) => {
            // `int` joins the signed machine carriers here: it is the lift
            // table's signed codomain, so `-1` and `0 - x` have to be spellable
            // at it. `Domain::admits_negative_values` is the question this site
            // actually asks, which `is_signed` (a question about the BitVec
            // carrier) only coincidentally answered before `int` existed.
            if !dom.admits_negative_values() {
                return Err(format!(
                    "unary negation is only supported for a signed machine binding or `int`, \
                     not `{}`",
                    dom.rust_name()
                ));
            }
            if let Some(magnitude) = nonneg_int_literal(&u.expr) {
                let mut literal = u.expr.as_ref();
                while let SynExpr::Paren(paren) = literal {
                    literal = &paren.expr;
                }
                if let SynExpr::Lit(literal) = literal {
                    if let Lit::Int(integer) = &literal.lit {
                        if !integer.suffix().is_empty()
                            && Domain::from_binding_ty(integer.suffix()).as_ref() != Some(dom)
                        {
                            return Err(format!("negative literal suffix `{}` disagrees with the operand carrier `{}`; \
                                use a matching literal type or an explicit checked conversion", integer.suffix(), dom.rust_name()));
                        }
                    }
                }
                return dom.negative_numeral(magnitude);
            }
            let value = elab_term(&u.expr, vars, offset, var_domains, dom)?;
            dom.arithmetic("sub", dom.zero(), value)
        }
        SynExpr::Binary(b) => {
            // `bool` has no arithmetic — `+ - * / %` over a boolean binding
            if matches!(dom, Domain::RegisteredAdt(_)) {
                return Err(dom.registered_operation_refusal("arithmetic and bitwise operations"));
            }
            // fail closed (only `==`/`!=`, the connectives, and a bare bool are
            // supported for `bool`).
            if dom.is_bool() {
                return Err("arithmetic is not supported for `bool` (only == != && || ! \
                            and a bare boolean variable)"
                    .into());
            }
            // `/` and `%` are admitted ONLY by a positive integer literal
            // divisor. A zero or variable divisor would make the executable
            // monitor divide by zero at runtime AND needs a `divisor != 0`
            // side-condition the elaborator cannot see. Both `/` and `%`
            // elaborate through the TOTAL `Nat.div`/`Nat.mod` — over a machine
            // width via the `toNat`/`ofNat` round-trip
            // (`<Carrier>.ofNat (Nat.div (<Carrier>.toNat x) c)`), so no
            // `UInt<W>.div`/`mod` prelude constant is needed and the result is
            // `< 2^width` so the round-trip is exact. A positive literal is
            // statically nonzero, so this total division matches Rust's trapping
            // division for every input.
            if matches!(b.op, BinOp::Div(_) | BinOp::Rem(_)) {
                if dom.is_signed() {
                    return Err(format!(
                        "signed division/remainder is not yet kernel-encoded for `{}`",
                        dom.rust_name()
                    ));
                }
                let Some(c) = positive_int_literal(&b.right) else {
                    return Err("division/remainder in a spec requires a positive integer \
                                literal divisor (a variable or zero divisor needs a nonzero \
                                side-condition, not yet wired)"
                        .into());
                };
                // The kernel encoding consumes the divisor as a Nat, but Rust
                // first checks that literal at the operand's machine type.
                // Preserve that source gate (`x / 300` is invalid for `u8`)
                // before projecting through `toNat`.
                let _ = dom.numeral(c)?;
                let nat_op = if matches!(b.op, BinOp::Div(_)) { "Nat.div" } else { "Nat.mod" };
                let nat_bin = |a: Expr, b: Expr| {
                    Expr::app(Expr::app(Expr::const_(Name::interned(nat_op), vec![]), a), b)
                };
                let dividend = elab_term(&b.left, vars, offset, var_domains, dom)?;
                let divisor = kernel_nat_lit(c);
                return Ok(match dom {
                    Domain::Nat => nat_bin(dividend, divisor),
                    Domain::Machine(width) => {
                        let to_nat = Expr::const_(Name::interned(width.to_nat_const()), vec![]);
                        let of_nat = Expr::const_(Name::interned(width.of_nat_const()), vec![]);
                        let nat_result = nat_bin(Expr::app(to_nat, dividend), divisor);
                        Expr::app(of_nat, nat_result)
                    }
                    Domain::U128 | Domain::USize(_) => {
                        let dividend = dom.bitvec_to_nat(dividend)?;
                        dom.bitvec_of_nat(nat_bin(dividend, divisor))?
                    }
                    Domain::Signed(_) | Domain::ISize(_) => {
                        return Err("signed division/remainder is not implemented".into());
                    }
                    // `Int` division is NOT the `Nat.div` encoding every other
                    // arm here uses, and Clean's `Int.div` rounds toward zero
                    // while `Int.emod` does not: two defensible answers, so the
                    // elaborator picks neither. Refused until the choice is
                    // ratified, which keeps the lift's codomain honest rather
                    // than silently adopting one convention.
                    Domain::Int => {
                        return Err("`/` and `%` are not supported at `int`; the rounding \
                                    convention for a negative operand is not settled, so the \
                                    elaborator refuses rather than choosing one. Options: do \
                                    the division inside a Lean definition, whose text states \
                                    the convention; or compare in `nat` when both operands are \
                                    known non-negative"
                            .into());
                    }
                    // Unreachable: bool arithmetic is rejected at the top of this
                    // arm. Fail closed rather than panic if a gate is ever missed.
                    Domain::Bool => return Err("arithmetic is not supported for `bool`".into()),
                    Domain::RegisteredAdt(_) => return Err(dom.registered_operation_refusal("division/remainder")),
                    Domain::OptionSigned(_) => {
                        return Err("arithmetic is not supported for an Option carrier".into());
                    }
                });
            }
            // A bit-shift by a LITERAL amount reduces to multiply / divide by a
            // power of two: `x << n = x * 2^n` (wrapping over a machine width,
            // exact over Nat) and `x >> n = x / 2^n` (truncated). This reuses the
            // `mul` / `div` machinery — no shift prelude constant is needed. The
            // amount must be a literal (so `2^n` is known) and, over a machine
            // width, `< width` (Rust rejects an over-width shift).
            if matches!(b.op, BinOp::Shl(_) | BinOp::Shr(_)) {
                let Some(n) = nonneg_int_literal(&b.right) else {
                    return Err("a bit-shift in a spec requires a literal shift amount".into());
                };
                if let Some(bits) = dom.shift_width_bits() {
                    if n >= u128::from(bits) {
                        return Err(format!(
                            "shift amount {n} is out of range for `{}` (must be < {})",
                            dom.rust_name(),
                            bits
                        ));
                    }
                }
                if dom.is_signed() && matches!(b.op, BinOp::Shr(_)) {
                    return Err(format!(
                        "signed right shift is not yet kernel-encoded for `{}`",
                        dom.rust_name()
                    ));
                }
                // Do not narrow `n` with `as`: amounts above `u32::MAX`
                // would wrap modulo 2^32 before `checked_shl` saw them.
                let shift = u32::try_from(n).map_err(|_| {
                    format!("shift amount {n} is too large for this fragment (>= 128)")
                })?;
                let two_pow_n = 1u128.checked_shl(shift).ok_or_else(|| {
                    format!("shift amount {n} is too large for this fragment (>= 128)")
                })?;
                let l = elab_term(&b.left, vars, offset, var_domains, dom)?;
                return Ok(match b.op {
                    BinOp::Shl(_) => {
                        if dom.is_signed() {
                            let value = Expr::apps(
                                Expr::const_(Name::interned("Nat.mul"), vec![]),
                                [dom.bitvec_to_nat(l)?, kernel_nat_lit(two_pow_n)],
                            );
                            dom.bitvec_of_nat(value)?
                        } else {
                            let r = dom.numeral(two_pow_n)?;
                            dom.arithmetic("mul", l, r)?
                        }
                    }
                    _ => {
                        let divisor = kernel_nat_lit(two_pow_n);
                        let nat_div = |a: Expr, b: Expr| {
                            Expr::app(
                                Expr::app(Expr::const_(Name::interned("Nat.div"), vec![]), a),
                                b,
                            )
                        };
                        match dom {
                            Domain::Nat => nat_div(l, divisor),
                            Domain::Machine(width) => {
                                let to_nat =
                                    Expr::const_(Name::interned(width.to_nat_const()), vec![]);
                                let of_nat =
                                    Expr::const_(Name::interned(width.of_nat_const()), vec![]);
                                Expr::app(of_nat, nat_div(Expr::app(to_nat, l), divisor))
                            }
                            Domain::U128 | Domain::USize(_) => {
                                let value = nat_div(dom.bitvec_to_nat(l)?, divisor);
                                dom.bitvec_of_nat(value)?
                            }
                            Domain::Signed(_) | Domain::ISize(_) => {
                                return Err("signed right shift is not implemented".into());
                            }
                            Domain::Int => {
                                return Err("bit-shift is not supported at `int`; an unbounded \
                                            integer has no bit width to shift within. Options: \
                                            shift at the machine type and lift the result; or \
                                            write the arithmetic in a Lean definition"
                                    .into());
                            }
                            Domain::Bool => {
                                return Err("bit-shift is not supported for `bool`".into());
                            }
                            Domain::RegisteredAdt(_) => return Err(dom.registered_operation_refusal("shifts")),
                            Domain::OptionSigned(_) => {
                                return Err(
                                    "bit-shift is not supported for an Option carrier".into()
                                );
                            }
                        }
                    }
                });
            }
            // Bitwise `&`/`|`/`^` elaborate through `Nat.land`/`Nat.lor`/
            // `Nat.xor`. Over a machine width the operands are `toNat`'d and the
            // result re-embedded with `ofNat` — the bitwise combination of two
            // `< 2^w` values is `< 2^w`, so the round-trip is exact and no
            // `UInt<W>` bitwise prelude constant is needed.
            if matches!(b.op, BinOp::BitAnd(_) | BinOp::BitOr(_) | BinOp::BitXor(_)) {
                let nat_op = match b.op {
                    BinOp::BitAnd(_) => "Nat.land",
                    BinOp::BitOr(_) => "Nat.lor",
                    _ => "Nat.xor",
                };
                let nat_bin = |a: Expr, b: Expr| {
                    Expr::app(Expr::app(Expr::const_(Name::interned(nat_op), vec![]), a), b)
                };
                let l = elab_term(&b.left, vars, offset, var_domains, dom)?;
                let r = elab_term(&b.right, vars, offset, var_domains, dom)?;
                return Ok(match dom {
                    Domain::Nat => nat_bin(l, r),
                    Domain::Machine(width) => {
                        let to_nat = Expr::const_(Name::interned(width.to_nat_const()), vec![]);
                        let of_nat = Expr::const_(Name::interned(width.of_nat_const()), vec![]);
                        let ln = Expr::app(to_nat.clone(), l);
                        let rn = Expr::app(to_nat, r);
                        Expr::app(of_nat, nat_bin(ln, rn))
                    }
                    Domain::Signed(_) | Domain::U128 | Domain::USize(_) | Domain::ISize(_) => {
                        let ln = dom.bitvec_to_nat(l)?;
                        let rn = dom.bitvec_to_nat(r)?;
                        dom.bitvec_of_nat(nat_bin(ln, rn))?
                    }
                    Domain::Bool => {
                        return Err("bitwise operators are not supported for `bool`".into());
                    }
                    Domain::Int => {
                        return Err("bitwise operators are not supported at `int`; an unbounded \
                                    integer has no bit width, and the two's-complement reading \
                                    of a negative value is a bit pattern this domain \
                                    deliberately does not expose. Options: combine at the \
                                    machine type and lift the result; or write it in a Lean \
                                    definition"
                            .into());
                    }
                    Domain::RegisteredAdt(_) => return Err(dom.registered_operation_refusal("bitwise operations")),
                    Domain::OptionSigned(_) => {
                        return Err(
                            "bitwise operators are not supported for an Option carrier".into()
                        );
                    }
                });
            }
            // `-` denotes the DOMAIN's subtraction: truncated `Nat.sub`
            // (saturating at 0) over Nat, wrapping `<Carrier>.sub` over a
            // machine width — the same faithful-modeling discipline as `+`/`*`,
            // so an underflowing claim stays as (un)provable as the semantics
            // dictate rather than being rejected outright.
            let op = match b.op {
                BinOp::Add(_) => "add",
                BinOp::Sub(_) => "sub",
                BinOp::Mul(_) => "mul",
                _ => {
                    return Err("unsupported binary op in a term (only + - * & | ^ and / % by a \
                                positive literal)"
                        .into());
                }
            };
            let l = elab_term(&b.left, vars, offset, var_domains, dom)?;
            let r = elab_term(&b.right, vars, offset, var_domains, dom)?;
            dom.arithmetic(op, l, r)
        }
        // E6 (design §3.1/§1.2-1): a program-fn call is a definitional use —
        // admissible only with a certified Pure ∧ Total ∧ Deterministic ∧
        // NoPanic facet AND a kernel constant minted by the import step; a
        // non-admitted call fails closed with the E6 diagnostic below.
        SynExpr::Call(c) => {
            let callee = callee_path(c);
            // `Some(e)` is the Option CONSTRUCTOR former (checked-arith spec
            // §3.3) — CONSTRUCTORS ONLY: it builds `Option.some.{0} (BitVec N)
            // <inner>` with the inner term at the SIGNED payload carrier.
            // There is deliberately NO destructor former (`unwrap`, `match`,
            // `?` all stay fail-closed — §3.4). Recognized only at an
            // Option-carrier position; a call spelled `Some(..)` at any other
            // carrier keeps the ordinary fail-closed path below (`Some` is
            // never an admissible function name — the mangled kernel-import
            // namespace cannot collide with it).
            if callee == "Some" {
                if let Domain::OptionSigned(width) = dom {
                    if c.args.len() != 1 {
                        return Err("`Some(..)` takes exactly one argument".to_string());
                    }
                    let inner = &c.args[0];
                    let payload_dom = Domain::Signed(*width);
                    let payload = elab_term(inner, vars, offset, var_domains, &payload_dom)?;
                    return Ok(Expr::apps(
                        Expr::const_(Name::interned("Option.some"), vec![Level::zero()]),
                        [payload_dom.ty(), payload],
                    ));
                }
                return Err(format!(
                    "`Some(..)` is an Option constructor and needs an Option-carrier \
                     position (here the operand carrier is `{}`); it can appear only \
                     against an admitted checked-arithmetic result",
                    dom.rust_name()
                ));
            }
            // E6 brick 4: an ADMITTED call elaborates to its kernel constant
            // applied to the elaborated arguments. The constant carries a
            // kernel-rechecked defining equation (minted by the import step);
            // the ambient admission table gates on certified facets + a minted
            // constant, so this fires only for genuinely admitted functions.
            // I0: a callee spelling that a parameter of this function also
            // binds is a call of the binding in Rust, and is refused rather
            // than resolved against a same-named island definition.
            if let Some(admission) = ambient_call_admission(&callee)? {
                // Trust (ref-self I1): a VIEW import is not compositional. Its
                // arity is the FLATTENED one (`x_ref(self.x, self.y)`) while
                // Rust reads `x_ref` as taking one borrow, and rustc does not
                // type-check clause text — so an author-written call of it
                // would elaborate against a signature no Rust caller can
                // write. The ONE position it is for is the self-call
                // `elaborate_ensures` splices in for `result`, which is keyed
                // by `self_fn_spelling(def_path)` and round-tripped there.
                //
                // Decided BEFORE the capability and arity checks for the same
                // reason I3 is decided before arity: whether a use site may
                // name the symbol at all is the prior question.
                if admission.is_self_result_only() && !is_ambient_self_fn_key(&callee) {
                    return Err(view_import_unnameable_refusal(&callee, &admission));
                }
                // I3: the use-site capability is decided BEFORE arity —
                // whether a use site may name the symbol at all is a prior
                // question to whether it applied the right number of
                // arguments, and answering them in the other order tells an
                // author to fix an arity in a call they were never allowed to
                // write. A PROOF use site never fails here.
                if let Err(refusal) = admission.require_at(ambient_use_site(), &callee) {
                    return Err(refusal.to_string());
                }
                // Trust (E9-ODT-FACE-SELF-CALL-1): the contracted function's own
                // call (the substitute `ensures_goal_source` splices in for
                // `result`) names the clause's FLATTENED field rows, while a TG11
                // ODT import takes the struct. Only that call is rebuilt, through
                // the face constructor and after the capability gate above;
                // every other call keeps the arity refusal below.
                if is_ambient_self_fn_key(&callee) {
                    if let Some(applied) = odt_face_self_call::face_self_call(
                        &callee,
                        &admission,
                        c,
                        vars,
                        offset,
                        var_domains,
                    )? {
                        return Ok(applied);
                    }
                }
                if admission.arity != c.args.len() {
                    return Err(format!(
                        "admitted `{callee}` has arity {} but is applied to {} argument(s)",
                        admission.arity,
                        c.args.len()
                    ));
                }
                let mut applied = Expr::const_(Name::from_string(&admission.kernel_const), vec![]);
                // PER-PARAMETER TYPING (E6/E9 widening increment 8). When the
                // admission records the callee's DECLARED carriers, each
                // argument is typed by the authority that owns it — the clause
                // binding behind its variables — and the declared carrier is
                // the CHECK, never the source. Without a record every argument
                // keeps taking the one ambient `dom`, exactly as before.
                match &admission.carriers {
                    Some(carriers) if carriers.params.len() == admission.arity => {
                        for (i, arg) in c.args.iter().enumerate() {
                            // Trust (d1/B2, 2026-09-28): at `ClauseMode::Strict` a
                            // cast is never elaborated, so an argument carrying one
                            // is refused HERE, before `argument_domain` — which sees
                            // straight through a cast (`collect_vars`) and would
                            // otherwise report `x as nat` as "a `u16` term" against
                            // the declared carrier, describing an argument the
                            // author did not write. Error → error only: every such
                            // argument already failed further down (the cast arm is
                            // gated on the mode), and the head is the pre-existing
                            // `unsupported term shape`.
                            if !has_ambient_proof_lift() && contains_cast(arg) {
                                return Err(strict_mode_cast_argument_refusal(&callee, i, arg));
                            }
                            // A LIFTED argument answers for itself: the cast
                            // names the math type, and nothing else may. This
                            // branch is gated on the argument SYNTACTICALLY
                            // carrying a cast, so an argument without one takes
                            // `argument_domain` exactly as before.
                            //
                            // A LITERAL argument is the one other row that
                            // moves: an untyped literal has no machine type, so
                            // in a lifted clause it takes the DECLARED carrier's
                            // domain when that carrier has a unique preimage,
                            // rather than the sibling's. `nat_snd(x as nat,
                            // 300)` from a `u8` function is the shape — today
                            // the literal is typed `u8` by its sibling and the
                            // clause is refused. Where the pre-existing rule
                            // SUCCEEDS the two agree by construction: success
                            // requires `arg_dom.carrier() == declared`, and a
                            // `declared` with a unique preimage has exactly one
                            // domain with that carrier.
                            let declared_for_literal = &carriers.params[i];
                            let arg_dom = if has_ambient_proof_lift() && contains_cast(arg) {
                                match pinned_domain(arg, var_domains)? {
                                    TermPin::Pinned(d) => d,
                                    TermPin::LiteralOnly => {
                                        argument_domain(arg, c, var_domains, dom)?
                                    }
                                    TermPin::Unpinned(why) => {
                                        let src = quote::quote!(#arg).to_string();
                                        return Err(format!(
                                            "admitted `{callee}` parameter {i}: `{src}` is not \
                                             self-determined ({why}); a lift is never decided \
                                             from a sibling argument or from the enclosing \
                                             comparison"
                                        ));
                                    }
                                }
                            } else if (has_ambient_proof_lift()
                                || matches!(dom, Domain::RegisteredAdt(_)))
                                && matches!(
                                    pinned_domain(arg, var_domains)?,
                                    TermPin::LiteralOnly
                                )
                            {
                                match declared_for_literal.unique_domain() {
                                    Some(unique_dom) => unique_dom,
                                    None => argument_domain(arg, c, var_domains, dom)?,
                                }
                            } else {
                                argument_domain(arg, c, var_domains, dom)?
                            };
                            let declared = &carriers.params[i];
                            // A NESTED typed call whose result no declaration
                            // names a domain for (an island codomain `BitVec n`,
                            // which `iN`, `u128` and the pointer-sized integers
                            // share). `arg_dom` is then only the sibling or
                            // ambient fallback, not a fact about that result, so
                            // its carrier is not what is compared: the nested
                            // callee's DECLARED result carrier is, against this
                            // parameter's declared carrier. Two declarations, and
                            // no domain is read off either (I0). `arg_dom` stays
                            // the ambient the nested call's own arguments are
                            // elaborated under, each checked against that
                            // callee's declared parameter in turn.
                            if let Some(nested) = undetermined_call_result_carrier(arg)? {
                                if nested != *declared {
                                    return Err(format!(
                                        "admitted `{callee}` declares parameter {i} at carrier \
                                         `{}`, but the argument is a call declared to return \
                                         carrier `{}`; a clause call is checked against the \
                                         callee's declared type and is never coerced to it",
                                        declared.clean_name(),
                                        nested.clean_name()
                                    ));
                                }
                                applied = Expr::app(
                                    applied,
                                    elab_term(arg, vars, offset, var_domains, &arg_dom)?,
                                );
                                continue;
                            }
                            if arg_dom.carrier() != *declared {
                                // Before repeating the "never coerced" message,
                                // say the USEFUL thing when the mismatch is
                                // exactly the one the lift table is about.
                                if has_ambient_proof_lift() {
                                    let src = quote::quote!(#arg).to_string();
                                    if let Some(to) = match declared.unique_domain() {
                                        Some(Domain::Nat) => Some(MathTy::Nat),
                                        Some(Domain::Int) => Some(MathTy::Int),
                                        _ => None,
                                    } {
                                        // D-11 (and D-1/D-12 through the table):
                                        // a machine term at a math-declared
                                        // parameter. The implicit lift is
                                        // decision OR-1, so name the cast to write
                                        // — or, when no lift exists at all, say
                                        // why it does not.
                                        return Err(match lift_for(&arg_dom, to) {
                                            Ok(_) => LiftRefusal::CastRequired
                                                .message(&src, &arg_dom, to),
                                            Err(refusal) => {
                                                refusal.message(&src, &arg_dom, to)
                                            }
                                        });
                                    }
                                    if arg_dom.is_math() {
                                        // D-2: the declared parameter is a
                                        // machine carrier and the argument is
                                        // an unbounded math term. The DECLARED
                                        // carrier travels into the message —
                                        // naming the math type on both sides
                                        // would say nothing.
                                        return Err(LiftRefusal::Narrowing(declared.clone())
                                            .message(
                                                &src,
                                                &arg_dom,
                                                if arg_dom == Domain::Int {
                                                    MathTy::Int
                                                } else {
                                                    MathTy::Nat
                                                },
                                            ));
                                    }
                                }
                                return Err(format!(
                                    "admitted `{callee}` declares parameter {i} at carrier `{}`, \
                                     but the argument is a `{}` term (carrier `{}`); a clause \
                                     call is checked against the callee's declared type and is \
                                     never coerced to it",
                                    declared.clean_name(),
                                    arg_dom.rust_name(),
                                    arg_dom.carrier().clean_name()
                                ));
                            }
                            applied =
                                Expr::app(applied, elab_term(arg, vars, offset, var_domains, &arg_dom)?);
                        }
                    }
                    // No record, or a record whose length contradicts the
                    // recorded arity (two independent reads of one declaration
                    // disagreeing — never indexed into, always fail-safe):
                    // the pre-increment behaviour, unchanged.
                    Some(_) | None => {
                        for arg in &c.args {
                            applied =
                                Expr::app(applied, elab_term(arg, vars, offset, var_domains, dom)?);
                        }
                    }
                }
                return Ok(applied);
            }
            Err(format!(
                "call to `{callee}` in a spec requires a sealed kernel admission for established Pure ∧ Total ∧ Deterministic ∧ NoPanic facets (E6); no production admission path is available, so program-function calls in specs fail closed; mention the function through its operational relation instead"
            ))
        }
        // THE EXPLICIT LIFT (nat-lift design §3.3), the ratified `e as nat` /
        // `e as int` spelling of spec surface §12.3.
        //
        // Outside [`ClauseMode::ProofLift`] this arm is not taken at all and a
        // cast keeps the pre-existing `unsupported term shape` message, to the
        // byte — the mode is the gate, so no existing elaboration changes.
        SynExpr::Cast(cast) if has_ambient_proof_lift() => {
            let Some(target) = MathTy::from_syn_type(&cast.ty) else {
                let ty = &cast.ty;
                return Err(non_spec_cast_error(&quote::quote!(#ty).to_string()));
            };
            // The cast's VALUE has the target's type, so the position it sits
            // in must be at that type. A cast at a machine position is exactly
            // the narrowing the table refuses (D-2), reported where the author
            // wrote it rather than as a downstream ill-typed goal.
            if *dom != target.domain() {
                let inner = &cast.expr;
                let operand_src = quote::quote!(#inner).to_string();
                return Err(LiftRefusal::Narrowing(dom.carrier()).message(
                    &format!("{operand_src} as {}", target.spelling()),
                    &target.domain(),
                    target,
                ));
            }
            match pinned_domain(&cast.expr, var_domains)? {
                // An untyped literal has no machine type of its own; the only
                // type in sight is the cast's, so `300 as nat` is the `Nat`
                // literal and `(200 + 100) as nat` is `Nat.add 200 100`. This
                // fires only where today is an error.
                TermPin::LiteralOnly => {
                    elab_term(&cast.expr, vars, offset, var_domains, &target.domain())
                }
                TermPin::Pinned(from) => {
                    let lift = lift_for(&from, target).map_err(|r| {
                        let inner = &cast.expr;
                        r.message(&quote::quote!(#inner).to_string(), &from, target)
                    })?;
                    record_required_signed_lift(&lift);
                    // The operand is elaborated at ITS OWN domain — spec
                    // surface §1.2 rule 4: `(a + b) as nat` means
                    // `toNat (a +wrap b)`, NOT unbounded addition.
                    let inner = elab_term(&cast.expr, vars, offset, var_domains, &from)?;
                    lift.wrap(inner)
                }
                TermPin::Unpinned(why) => {
                    let inner = &cast.expr;
                    let operand_src = quote::quote!(#inner).to_string();
                    Err(unpinned_lift_error(&operand_src, target, &why))
                }
            }
        }
        SynExpr::MethodCall(m) => Err(format!(
            "method call `.{}(..)` in a spec requires a sealed kernel admission for established Pure ∧ Total ∧ Deterministic ∧ NoPanic facets (E6); method identity and admission are not available, so method calls in specs fail closed; mention the method through its operational relation instead",
            m.method
        )),
        _ => Err("unsupported term shape".into()),
    }
}

/// Elaborate a predicate into a `Prop`-valued CIC term at the given binder
/// `offset`, over arithmetic domain `dom`. Shared by whole-goal and contract
/// elaboration.
fn elaborate_prop(
    ast: &SynExpr,
    vars: &[String],
    offset: u32,
    dom: &Domain,
) -> Result<Expr, String> {
    // SINGLE-DOMAIN LANE. Every variable of this clause carries `dom`, so the
    // per-variable map that [`elab_term`] now consults is the uniform one —
    // which makes every operand's typing here byte-identical to the
    // pre-increment code, entry point for entry point.
    let uniform = uniform_var_domains(vars, dom);
    elaborate_prop_with_uniform(ast, vars, offset, dom, &uniform)
}

fn elaborate_prop_with_uniform(
    ast: &SynExpr,
    vars: &[String],
    offset: u32,
    dom: &Domain,
    var_domains: &BTreeMap<String, Domain>,
) -> Result<Expr, String> {
    match ast {
        SynExpr::Paren(p) => elaborate_prop_with_uniform(&p.expr, vars, offset, dom, var_domains),
        // Logical connectives: operands are *propositions* — recurse.
        SynExpr::Unary(u) if matches!(u.op, syn::UnOp::Not(_)) => Ok(Expr::app(
            Expr::const_(Name::interned("Not"), vec![]),
            elaborate_prop_with_uniform(&u.expr, vars, offset, dom, var_domains)?,
        )),
        SynExpr::Binary(b) if matches!(b.op, BinOp::And(_)) => Ok(connective(
            "And",
            elaborate_prop_with_uniform(&b.left, vars, offset, dom, var_domains)?,
            elaborate_prop_with_uniform(&b.right, vars, offset, dom, var_domains)?,
        )),
        SynExpr::Binary(b) if matches!(b.op, BinOp::Or(_)) => Ok(connective(
            "Or",
            elaborate_prop_with_uniform(&b.left, vars, offset, dom, var_domains)?,
            elaborate_prop_with_uniform(&b.right, vars, offset, dom, var_domains)?,
        )),
        // Disequality `a != b` desugars to `!(a == b)` (see `ne_as_not_eq`).
        SynExpr::Binary(b) if matches!(b.op, BinOp::Ne(_)) => {
            elaborate_prop_with_uniform(&ne_as_not_eq(b), vars, offset, dom, var_domains)
        }
        // A bare identifier — or a dotted path naming a `bool` FIELD — is a
        // proposition only in a `bool` clause, where `flag` is read as
        // `flag = true`.
        SynExpr::Path(_) | SynExpr::Field(_) if dom.is_bool() => {
            let v = elab_term(ast, vars, offset, var_domains, dom)?;
            Ok(dom.eq(v, dom.bool_lit(true)?))
        }
        // A boolean literal is the trivial proposition `True`/`False`.
        SynExpr::Lit(l) if matches!(&l.lit, Lit::Bool(_)) => {
            let value = matches!(&l.lit, Lit::Bool(b) if b.value);
            Ok(Expr::const_(Name::interned(if value { "True" } else { "False" }), vec![]))
        }
        // Comparison predicate `a <cmp> b`: operands are *terms*.
        SynExpr::Binary(b) => {
            // BOOL-CARRIER EQUALITY, kept byte-identical to the multi-domain
            // lane's arm (see the commentary there) so a single-domain clause
            // elaborates to the same term through either entry point.
            let decided_side =
                decided_bool_form(&b.left, var_domains) || decided_bool_form(&b.right, var_domains);
            if matches!(b.op, BinOp::Eq(_)) && decided_side {
                let l = elab_bool_term(&b.left, vars, offset, var_domains)?;
                let r = elab_bool_term(&b.right, vars, offset, var_domains)?;
                return Ok(Domain::Bool.eq(l, r));
            }
            // `bool` is unordered — only `==`/`!=` decide it. That applies to a
            // decided bool-valued operand exactly as it does to a `bool`
            // binding.
            if matches!(b.op, BinOp::Le(_) | BinOp::Lt(_) | BinOp::Ge(_) | BinOp::Gt(_))
                && (dom.is_bool() || decided_side)
            {
                return Err("`bool` values are not ordered (use `==` or `!=`)".into());
            }
            if matches!(dom, Domain::RegisteredAdt(_)) && !matches!(b.op, BinOp::Eq(_)) {
                return Err(dom.registered_operation_refusal("ordering"));
            }
            let l = elab_term(&b.left, vars, offset, var_domains, dom)?;
            let r = elab_term(&b.right, vars, offset, var_domains, dom)?;
            Ok(match b.op {
                BinOp::Eq(_) => dom.eq(l, r),
                BinOp::Le(_) => dom.cmp("le", l, r),
                BinOp::Lt(_) => dom.cmp("lt", l, r),
                BinOp::Ge(_) => dom.cmp("le", r, l), // a >= b  ≡  b <= a
                BinOp::Gt(_) => dom.cmp("lt", r, l), // a >  b  ≡  b <  a
                _ => return Err("comparison op must be one of == != <= < >= >".into()),
            })
        }
        // E6 (two-language design §3.1, v3 ruling: NO surface marker): a
        // program-function call is a definitional use and therefore requires a
        // sealed, item-bound kernel import. Public
        // `Pure ∧ Total ∧ Deterministic ∧ NoPanic` findings are only
        // diagnostics; they neither define the function in Clean nor mint
        // admission authority.
        //
        // A call to an ADMITTED `-> bool` function is the one call shape that
        // is a proposition on its own, read as `f(a, b) = true` — the same
        // reading a bare `bool` binding gets. Its admission recorded a
        // `Domain::Bool` return at mint time, so no re-derivation and no
        // guessing is involved. EVERY other call in proposition position is
        // outside the admitted fragment and fails CLOSED with the diagnostic
        // below, unchanged.
        SynExpr::Call(c) if call_ret_domain(c).is_some_and(|d| d.is_bool()) => {
            let v = elab_term(ast, vars, offset, var_domains, dom)?;
            Ok(Domain::Bool.eq(v, Domain::Bool.bool_lit(true)?))
        }
        SynExpr::Call(c) => {
            let callee = callee_path(c);
            Err(format!(
                "call to `{callee}` in a spec requires a sealed, item-bound kernel \
                 admission binding its definition and established Pure ∧ Total ∧ \
                 Deterministic ∧ NoPanic proofs (E6); public facet findings are \
                 diagnostic only and no production admission path exists, so \
                 program-function calls in specs fail closed; mention the function \
                 through its operational relation instead"
            ))
        }
        SynExpr::MethodCall(m) => Err(format!(
            "method call `.{}(..)` in a spec requires resolved item identity and a \
             sealed, item-bound kernel admission binding its definition and established \
             Pure ∧ Total ∧ Deterministic ∧ NoPanic proofs (E6); public facet \
             findings are diagnostic only and no production admission path exists, so \
             method calls in specs fail closed; mention the method through its \
             operational relation instead",
            m.method
        )),
        _ => Err("predicate must be a comparison or a connective (&& || !)".into()),
    }
}

/// `pred a b` for a binary Nat relation constant (`Nat.le` / `Nat.lt`).
fn nat_pred(name: &str, a: Expr, b: Expr) -> Expr {
    Expr::app(Expr::app(Expr::const_(Name::interned(name), vec![]), a), b)
}

/// `And p q` / `Or p q` — the propositional connectives (`Prop → Prop → Prop`).
fn connective(name: &str, p: Expr, q: Expr) -> Expr {
    Expr::app(Expr::app(Expr::const_(Name::interned(name), vec![]), p), q)
}

/// Wrap a `Prop` body (built over `vars` at the body depth) in
/// `∀ (v0..vn : <dom>)`.
fn close_over(vars: &[String], body: Expr, dom: &Domain) -> Expr {
    let mut goal = body;
    for _ in vars {
        goal = Expr::pi(BinderInfo::Default, dom.ty(), goal);
    }
    goal
}

/// Elaborate a whole spec predicate into a closed goal
/// `∀ (v0 .. vn : Nat), <prop>`. Fail-closed outside the supported fragment.
pub fn elaborate_goal(spec: &str) -> Result<Expr, String> {
    elaborate_goal_in(spec, &Domain::Nat)
}

/// Elaborate a whole spec predicate over an explicit arithmetic domain.
/// For `Domain::Machine(_)` the resulting mathematical statement uses the
/// corresponding fixed-width wrapping carrier. This API does not bind that
/// statement to a Rust/Trust-IR obligation and grants no VC authority.
pub fn elaborate_goal_in(spec: &str, dom: &Domain) -> Result<Expr, String> {
    if matches!(dom, Domain::RegisteredAdt(_)) {
        return Err("registered datatype clauses require current-environment validation; use elaborate_goal_with_domains with the checking Environment".into());
    }
    let ast: SynExpr = syn::parse_str(spec).map_err(|e| format!("parse error: {e}"))?;
    let mut vars = Vec::new();
    collect_vars(&ast, &mut vars);
    Ok(close_over(&vars, elaborate_prop(&ast, &vars, 0, dom)?, dom))
}

/// Elaborate a statement with an exact set of named variable bindings.
///
/// `var_types` must be a bijection with the predicate's free identifiers:
/// duplicates, missing names, extra names, unsupported types, and mixed
/// arithmetic domains all fail closed. In particular, an empty binding list
/// never guesses that free variables are `Nat`, and `Nat` is not a wildcard
/// that coerces machine variables. The current fragment deliberately supports
/// one homogeneous domain per statement; a future per-expression type checker
/// may safely widen that surface.
///
/// The binding strings are a compatibility surface, not an authoritative Rust
/// type identity. Callers must not turn this returned expression into Rust VC
/// evidence until the bindings come from—and the checked theorem is digest-
/// bound to—a canonical typed Trust-IR obligation.
pub fn elaborate_goal_typed(spec: &str, var_types: &[(&str, &str)]) -> Result<Expr, String> {
    // E3: a clause spelled in the quantifier fragment (a `forall`/`exists`
    // binder head or a `==>` implication) takes the quantified path; everything
    // else stays on the original path byte-for-byte.
    if clause_uses_quantifier_fragment(spec) {
        return elaborate_quantified_goal_typed(spec, var_types);
    }
    let ast: SynExpr = syn::parse_str(spec).map_err(|e| format!("parse error: {e}"))?;
    elaborate_parsed_goal_typed(&ast, var_types)
}

fn elaborate_parsed_goal_typed(
    ast: &SynExpr,
    var_types: &[(&str, &str)],
) -> Result<Expr, String> {
    let vars = collect_exact_clause_vars(ast, var_types)?;
    let var_domains = exact_typed_bindings(&vars, var_types)?;
    let body = elaborate_prop_multi(ast, &vars, 0, &var_domains)?;
    close_over_multi(&vars, body, &var_domains)
}

/// Elaborate exact typed bindings, including registered kernel datatypes, in
/// the environment that will check the resulting proposition. Unlike the
/// string compatibility API, a datatype cannot be admitted by spelling its
/// name. Every registered handle in the bindings and facet table is revalidated
/// here; the complete goal is then fully checked as `Prop`.
///
/// This is mathematical goal construction, not Rust VC authority. In
/// particular, it neither proves a Rust representation relation nor promotes
/// a reflected admission to `KernelChecked`.
pub fn elaborate_goal_with_domains(
    env: &Environment,
    spec: &str,
    var_domains: &[(&str, Domain)],
    facets: &FacetTable,
) -> Result<Expr, String> {
    elaborate_goal_with_domains_inner(env, spec, None, var_domains, facets, None)
}

fn elaborate_goal_with_domains_inner(
    env: &Environment,
    spec: &str,
    parsed_ast: Option<&SynExpr>,
    bindings: &[(&str, Domain)],
    facets: &FacetTable,
    self_fn_name: Option<&str>,
) -> Result<Expr, String> {
    for (_, domain) in bindings {
        domain.validate_in(env)?;
    }
    // A facet table can outlive the environment it was read from. Revalidate
    // the carriers even when they occur only as a call's result or parameter.
    for admission in facets.records.admissions.values() {
        if let Some(domain) = admission.return_domain() {
            domain.validate_in(env)?;
        }
        if let Some(carriers) = &admission.carriers {
            for carrier in carriers.params.iter().chain(std::iter::once(&carriers.ret)) {
                carrier.validate_in(env)?;
            }
        }
    }
    let _lift = ProofLiftScope::enter(&ProofClauseInputs::strict(), self_fn_name);
    let _self_fn = SelfFnScope::enter(self_fn_name);
    let _scope = AdmissionScope::enter_at(facets.clone(), trust_symbols::Capability::Proof);
    let goal = if parsed_ast.is_none() && clause_uses_quantifier_fragment(spec) {
        let clause = parse_qclause(spec, true)?;
        if let Some(err) = qclause_first_call_facet_error(&clause, facets) {
            return Err(err);
        }
        let mut free = Vec::new();
        collect_qclause_free_vars(&clause, &mut Vec::new(), &mut free);
        let mut domains = exact_domain_bindings(&free, bindings)?;
        let body = elab_qclause(&clause, &mut free.clone(), 0, &mut domains)?;
        close_over_multi(&free, body, &domains)?
    } else if let Some(ast) = parsed_ast {
        let vars = collect_exact_clause_vars(ast, bindings)?;
        if let Some(err) = first_call_facet_error(ast, facets) {
            return Err(err);
        }
        let domains = exact_domain_bindings(&vars, bindings)?;
        let body = elaborate_prop_multi(ast, &vars, 0, &domains)?;
        close_over_multi(&vars, body, &domains)?
    } else {
        let (ast, vars) = parse_exact_clause_vars(spec, bindings)?;
        if let Some(err) = first_call_facet_error(&ast, facets) {
            return Err(err);
        }
        let domains = exact_domain_bindings(&vars, bindings)?;
        let body = elaborate_prop_multi(&ast, &vars, 0, &domains)?;
        close_over_multi(&vars, body, &domains)?
    };
    clean_kernel::TypeChecker::new(env).check_type(&goal, &Expr::prop()).map_err(|err| {
        format!("typed clause is not a proposition in the current environment: {err}")
    })?;
    Ok(goal)
}

/// Environment-aware `ensures` for exact domains. Shares the existing
/// parameter-order and self-identity checks and substitutes the admitted
/// self-call for `result`; it never quantifies over an unconstrained result.
pub fn elaborate_ensures_with_domains(
    env: &Environment,
    clause: &str,
    param_domains: &[(&str, Domain)],
    self_fn_name: &str,
    facets: &FacetTable,
) -> Result<Expr, String> {
    // Validate even unused parameters before reducing to the clause's free
    // inputs, so filtering cannot hide a stale datatype handle.
    for (_, domain) in param_domains {
        domain.validate_in(env)?;
    }
    let source = ensures_goal_source(clause, param_domains, self_fn_name, facets)?;
    let used = discharge_used_bindings(&source, param_domains);
    elaborate_goal_with_domains_inner(
        env,
        &source.src,
        source.parsed_ast.as_ref(),
        &used,
        facets,
        Some(self_fn_name),
    )
}

/// R4 §2 (evidence-carrying binder inference, ratified 2026-07-22): the E3
/// closed binder-type set, in probe order. Exactly `Domain::from_binding_ty`'s
/// vocabulary — a probe outcome is meaningful only against the same set the
/// clause grammar admits.
pub const E3_BINDER_TYPES: [&str; 18] = [
    "nat", "u8", "u16", "u32", "u64", "u128", "i8", "i16", "i32", "i64", "i128", "usize16",
    "usize32", "usize64", "isize16", "isize32", "isize64", "bool",
];

/// R4 §2: probe which E3 binder types make an untyped quantifier clause
/// elaborate. MEASUREMENT ONLY — this returns the full outcome vector and
/// applies nothing. The one-engine discipline: the same elaborator that will
/// discharge the ported clause judges every candidate typing, and a caller
/// may treat a typing as an inference witness ONLY when it is the unique
/// success (zero successes = no admissible typing; two or more = ambiguous —
/// both refuse). Auto-application into ported sources additionally waits for
/// the bounded-domain encoding: a unique NATIVE typing does not by itself
/// prove the pearlite (Int-relaxed) reading meant the same predicate, and
/// guessing there is the exactness failure the doctrine forbids.
pub fn probe_untyped_binder_typings(
    quantifier: &str,
    binder: &str,
    body: &str,
    var_types: &[(&str, &str)],
) -> Vec<(&'static str, bool)> {
    E3_BINDER_TYPES
        .iter()
        .map(|ty| {
            let spec = format!("{quantifier} {binder}: {ty}, {body}");
            (*ty, elaborate_goal_typed(&spec, var_types).is_ok())
        })
        .collect()
}

// ---------------------------------------------------------------------------
// E3 — Lean-shaped quantifier binders + implication (two-language design §3.1
// ruling D3 / engine row E3).
//
// The surface fragment this pre-parser recognizes, CONSERVATIVELY:
//
//   clause := "forall" IDENT ":" TY "," clause     (one binder, clause head only)
//           | "exists" IDENT ":" TY "," clause     (one binder, clause head only)
//           | leaf "==>" clause                    (right-associative)
//           | leaf
//
// where TY is one of `E3_BINDER_TYPES` (exactly `Domain::from_binding_ty`)
// and a leaf is the existing syn-parsed fragment. Everything outside this shape
// fails CLOSED with a diagnostic: nested / non-head quantifiers, multi-binder
// heads (`forall i: u64, j: u64, …`), unsupported binder types, and a binder
// that shadows a clause parameter. `forall` / `exists` are reserved words in
// clause-head position; `==>` never parses as Rust, so its presence always
// selects this fragment.
//
// Kernel elaboration (§ the design's Lean-shaped binders ruling):
//   forall x: T, P   →  Expr::pi   (T, P)            — the CIC dependent ∀
//   exists x: T, P   →  Exists.{1} T (fun x: T => P) — the prelude inductive
//                       (`Exists : {α : Sort u} → (α → Prop) → Prop`, α at
//                       Sort 1 for every supported carrier)
//   A ==> B          →  Expr::pi   (A, B)            — the Prop arrow, exactly
//                       how `elaborate_contract_in` builds `pre → post`
//
// De Bruijn discipline: a quantifier binder is APPENDED to `vars` for its body
// (the last variable is the innermost binder — `elab_term`'s convention), and
// each `==>` arrow elaborates its RHS one `offset` deeper (the arrow's unused
// binder), mirroring the existing contract path. The reduction-pinning tests
// (`quantifier_de_bruijn_indices_are_pinned`, `forall_true_instance_reduces`)
// hold this arithmetic in place.
// ---------------------------------------------------------------------------

/// Which quantifier a [`QClause::Quant`] head binds.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum QuantKind {
    Forall,
    Exists,
}

/// A clause in the E3 quantifier fragment, pre-parsed ahead of syn.
enum QClause {
    /// `forall|exists <var>: <ty>, <body>` — one binder, clause head only.
    Quant { kind: QuantKind, var: String, ty: String, body: Box<QClause> },
    /// `<lhs> ==> <rhs>` — the Prop arrow, right-associative.
    Implies { lhs: Box<QClause>, rhs: Box<QClause> },
    /// A leaf inside the existing syn-parsed fragment.
    Leaf(SynExpr),
}

/// Whether a clause is spelled in the quantifier fragment and must take the E3
/// pre-parsed path. `forall`/`exists` are reserved in clause-head position
/// (also behind outer parentheses); `==>` is not Rust syntax, so any occurrence
/// selects this path (a malformed use then fails closed in the pre-parser
/// rather than as an inscrutable syn error).
fn clause_uses_quantifier_fragment(spec: &str) -> bool {
    let t = strip_outer_parens(spec.trim());
    strip_quant_keyword(t, "forall").is_some()
        || strip_quant_keyword(t, "exists").is_some()
        || spec.contains("==>")
}

/// `Some(rest)` iff `s` starts with the WORD `kw` (not a longer identifier such
/// as `forall_x`), where `rest` is everything after the keyword.
fn strip_quant_keyword<'a>(s: &'a str, kw: &str) -> Option<&'a str> {
    let rest = s.strip_prefix(kw)?;
    match rest.chars().next() {
        // The exact keyword is reserved too: route it through the E3 parser so
        // the missing-binder diagnostic wins even if a caller supplies a
        // forgeable free-variable binding named `forall` or `exists`.
        None => Some(rest),
        // `forallx`/`forall_`/`forall1` are ordinary identifiers.
        Some(c) if c.is_alphanumeric() || c == '_' => None,
        Some(_) => Some(rest),
    }
}

/// Strip MATCHED outer parentheses, repeatedly: `((P))` → `P`. A parenthesis
/// that closes before the end (`(a) ==> (b)`) is not outer and is kept.
///
/// Nesting is tracked as two `usize` counts over the bytes of `inner` (`(`
/// and `)` are ASCII, so a byte walk sees exactly the parentheses a `char`
/// walk would): the stripped pair is matched iff the closes never overtake
/// the opens. Each count is at most the byte index it was taken at, which is
/// what the `> i` guards restate — a loop-carried fact the verifier does not
/// carry for this loop shape (measured 2026-09-13 on `dff2b22d1`: the former
/// `i32` depth was refuted at `i32::MAX`, a real overflow at 2^31 nested
/// parentheses; the guarded counts prove).
fn strip_outer_parens(s: &str) -> &str {
    let mut t = s.trim();
    loop {
        let Some(inner) = t.strip_prefix('(').and_then(|r| r.strip_suffix(')')) else {
            return t;
        };
        let bytes = inner.as_bytes();
        let mut opens: usize = 0;
        let mut closes: usize = 0;
        let mut matched = true;
        let mut i: usize = 0;
        while i < bytes.len() {
            match bytes[i] {
                b'(' => {
                    if opens > i {
                        return t;
                    }
                    opens += 1;
                }
                b')' => {
                    if closes > i {
                        return t;
                    }
                    closes += 1;
                    // Depth `1 + opens - closes` returned to zero before the end.
                    if closes > opens {
                        matched = false;
                        break;
                    }
                }
                _ => {}
            }
            i += 1;
        }
        if !matched {
            return t;
        }
        t = inner.trim();
    }
}

/// Split `s` at the FIRST parenthesis-depth-zero `==>`, if any. With the
/// right-associative grammar the first split's LHS is a leaf (or a
/// parenthesized sub-clause) and the RHS may itself be an implication.
///
/// Depth is `opens - closes` over the bytes of `s` (both ASCII), so depth zero
/// is `opens == closes`; each count is at most the byte index it was taken
/// at, restated by the `> i` guards for the reason given at
/// [`strip_outer_parens`]. The two halves are taken with `str::get`: `i` and
/// `i + 3` sit on ASCII bytes and so on character boundaries, and `get` says
/// so in its return type where an index would panic on a boundary the
/// verifier cannot see (measured 2026-09-13 on `dff2b22d1`: the indexed
/// halves were refuted, the `get` halves prove).
fn split_top_level_implies(s: &str) -> Option<(&str, &str)> {
    let bytes = s.as_bytes();
    let mut opens: usize = 0;
    let mut closes: usize = 0;
    let mut i: usize = 0;
    while i < bytes.len() {
        match bytes[i] {
            b'(' => {
                if opens > i {
                    return None;
                }
                opens += 1;
            }
            b')' => {
                if closes > i {
                    return None;
                }
                closes += 1;
            }
            b'=' if opens == closes && bytes[i..].starts_with(b"==>") => {
                return Some((s.get(..i)?, s.get(i + 3..)?));
            }
            _ => {}
        }
        i += 1;
    }
    None
}

/// Pre-parse a clause in the quantifier fragment. `at_head` is true only for
/// the whole clause: a quantifier anywhere else (nested under another binder,
/// or as an implication operand) is outside this conservative first fragment
/// and fails closed.
fn parse_qclause(spec: &str, at_head: bool) -> Result<QClause, String> {
    let t = strip_outer_parens(spec.trim());
    for (kw, kind) in [("forall", QuantKind::Forall), ("exists", QuantKind::Exists)] {
        if let Some(rest) = strip_quant_keyword(t, kw) {
            if !at_head {
                return Err(format!(
                    "a `{kw}` binder is only supported at the head of a clause \
                     (nested quantifiers are not yet in the elaborated fragment)"
                ));
            }
            return parse_quant_binder(kind, kw, rest);
        }
    }
    if let Some((lhs, rhs)) = split_top_level_implies(t) {
        return Ok(QClause::Implies {
            lhs: Box::new(parse_qclause(lhs, false)?),
            rhs: Box::new(parse_qclause(rhs, false)?),
        });
    }
    let ast: SynExpr = syn::parse_str(t).map_err(|e| format!("parse error: {e}"))?;
    Ok(QClause::Leaf(ast))
}

/// Parse the `<ident>: <ty>, <body>` tail of a quantifier head.
fn parse_quant_binder(kind: QuantKind, kw: &str, rest: &str) -> Result<QClause, String> {
    let rest = rest.trim_start();
    let ident_end = rest
        .char_indices()
        .find(|&(_, c)| !(c.is_alphanumeric() || c == '_'))
        .map_or(rest.len(), |(i, _)| i);
    // `ident_end` is a `char_indices` index (or `rest.len()`), so it is a
    // character boundary; `split_at_checked` says so in its return type where
    // `split_at` would panic on a boundary the verifier cannot see.
    let Some((var, after)) = rest.split_at_checked(ident_end) else {
        return Err(format!("`{kw}` binder name does not end on a character boundary"));
    };
    if var.is_empty() || var.chars().next().is_some_and(|c| c.is_ascii_digit()) {
        return Err(format!("`{kw}` expects a binder name (e.g. `{kw} i: u64, <body>`)"));
    }
    let after = after.trim_start();
    let Some(after) = after.strip_prefix(':') else {
        return Err(format!(
            "`{kw} {var}` expects `: <type>` after the binder name \
             (e.g. `{kw} {var}: u64, <body>`)"
        ));
    };
    // The supported binder types contain no comma, so the type runs to the
    // first comma; the body is everything after it.
    let Some((ty, body_src)) = after.split_once(',') else {
        return Err(format!("`{kw} {var}: …` expects `, <body>` after the binder type"));
    };
    let ty = ty.trim();
    if ty.is_empty() {
        return Err(format!("`{kw} {var}:` is missing the binder type"));
    }
    // A second `name: ty` group after the comma is a multi-binder head — not a
    // body. The supported leaf fragment never contains a bare `:` (paths and
    // type ascription are outside it), so any depth-zero single `:` in the body
    // means a multi-binder spelling; fail closed with the precise diagnostic.
    // A body that is itself a quantifier head also carries a `:`, but that is
    // the NESTED-quantifier case — let the recursion report it precisely.
    let body_head = strip_outer_parens(body_src.trim());
    let body_is_nested_quant = strip_quant_keyword(body_head, "forall").is_some()
        || strip_quant_keyword(body_head, "exists").is_some();
    if !body_is_nested_quant && body_has_top_level_colon(body_src) {
        return Err(format!(
            "`{kw}` with multiple binders is not yet supported \
             (bind one variable per quantifier)"
        ));
    }
    Ok(QClause::Quant {
        kind,
        var: var.to_string(),
        ty: ty.to_string(),
        body: Box::new(parse_qclause(body_src, false)?),
    })
}

/// Whether `s` has a parenthesis-depth-zero single `:` (`::` path separators,
/// which the fragment rejects later anyway, are not flagged here).
///
/// Same counting discipline as [`split_top_level_implies`]. A `::` is stepped
/// over with one `i += 2` behind a length check, so the step stays inside the
/// slice, rather than two increments: the verifier proves a single bounded
/// step from the loop condition and refuted the two-step spelling (measured
/// 2026-09-13 on `dff2b22d1`).
fn body_has_top_level_colon(s: &str) -> bool {
    let bytes = s.as_bytes();
    let mut opens: usize = 0;
    let mut closes: usize = 0;
    let mut i: usize = 0;
    while i < bytes.len() {
        match bytes[i] {
            b'(' => {
                if opens > i {
                    return true;
                }
                opens += 1;
            }
            b')' => {
                if closes > i {
                    return true;
                }
                closes += 1;
            }
            b':' if opens == closes => {
                if bytes.len() - i >= 2 && bytes[i..].starts_with(b"::") {
                    i += 2; // skip `::`
                    continue;
                }
                return true;
            }
            _ => {}
        }
        i += 1;
    }
    false
}

/// Free identifiers of a pre-parsed clause in first-appearance order —
/// [`collect_vars`] per leaf, minus the quantifier binders in scope.
fn collect_qclause_free_vars(clause: &QClause, bound: &mut Vec<String>, out: &mut Vec<String>) {
    match clause {
        QClause::Leaf(ast) => {
            let mut vs = Vec::new();
            collect_vars(ast, &mut vs);
            for v in vs {
                if !bound.contains(&v) && !out.contains(&v) {
                    out.push(v);
                }
            }
        }
        QClause::Implies { lhs, rhs } => {
            collect_qclause_free_vars(lhs, bound, out);
            collect_qclause_free_vars(rhs, bound, out);
        }
        QClause::Quant { var, body, .. } => {
            bound.push(var.clone());
            collect_qclause_free_vars(body, bound, out);
            bound.pop();
        }
    }
}

/// Quantifier binder names occurring in a pre-parsed clause. The current
/// conservative grammar permits only a head binder, but walking recursively
/// keeps the signature-shadowing gate correct if that grammar is extended.
fn collect_qclause_binders(clause: &QClause, out: &mut Vec<String>) {
    match clause {
        QClause::Leaf(_) => {}
        QClause::Implies { lhs, rhs } => {
            collect_qclause_binders(lhs, out);
            collect_qclause_binders(rhs, out);
        }
        QClause::Quant { var, body, .. } => {
            if !out.contains(var) {
                out.push(var.clone());
            }
            collect_qclause_binders(body, out);
        }
    }
}

/// The E6 facet diagnostic walk over a pre-parsed clause's leaves (the
/// quantified counterpart of running [`first_call_facet_error`] on the whole
/// syn AST).
fn qclause_first_call_facet_error(clause: &QClause, facets: &FacetTable) -> Option<String> {
    match clause {
        QClause::Leaf(ast) => first_call_facet_error(ast, facets),
        QClause::Implies { lhs, rhs } => qclause_first_call_facet_error(lhs, facets)
            .or_else(|| qclause_first_call_facet_error(rhs, facets)),
        QClause::Quant { body, .. } => qclause_first_call_facet_error(body, facets),
    }
}

/// Elaborate a pre-parsed clause at binder `offset`. A quantifier binder is
/// APPENDED to `vars` (and its domain to `var_domains`) for the body — the last
/// variable is the innermost binder, `elab_term`'s de Bruijn convention — and
/// removed afterwards; an implication elaborates its RHS one `offset` deeper
/// (under the arrow's unused binder), exactly like `elaborate_contract_in`.
fn elab_qclause(
    clause: &QClause,
    vars: &mut Vec<String>,
    offset: u32,
    var_domains: &mut BTreeMap<String, Domain>,
) -> Result<Expr, String> {
    match clause {
        QClause::Leaf(ast) => elaborate_prop_multi(ast, vars, offset, var_domains),
        QClause::Implies { lhs, rhs } => {
            let l = elab_qclause(lhs, vars, offset, var_domains)?;
            let r = elab_qclause(rhs, vars, one_binder_deeper(offset)?, var_domains)?;
            Ok(Expr::pi(BinderInfo::Default, l, r))
        }
        QClause::Quant { kind, var, ty, body } => {
            let dom = Domain::from_binding_ty(ty).ok_or_else(|| {
                format!(
                    "unsupported quantifier binder type `{ty}` \
                     (supported: {})",
                    E3_BINDER_TYPES.join(", ")
                )
            })?;
            // A binder that collides with a clause parameter (or any name
            // already in scope) would silently capture its occurrences — fail
            // closed instead of choosing a shadowing semantics.
            if var_domains.contains_key(var) {
                return Err(format!(
                    "quantifier binder `{var}` shadows a clause variable of the same name; \
                     rename the binder"
                ));
            }
            vars.push(var.clone());
            var_domains.insert(var.clone(), dom.clone());
            let body_expr = elab_qclause(body, vars, offset, var_domains);
            vars.pop();
            var_domains.remove(var);
            let body_expr = body_expr?;
            Ok(match kind {
                QuantKind::Forall => Expr::pi(BinderInfo::Default, dom.ty(), body_expr),
                // `Exists : {α : Sort u} → (α → Prop) → Prop` (the prelude
                // inductive; see clean-kernel `init_exists`). Every supported
                // carrier lives in Type 0 = Sort 1, so u = 1, and the two
                // explicit-position arguments are the carrier and the
                // predicate lambda.
                QuantKind::Exists => Expr::app(
                    Expr::app(
                        Expr::const_(Name::interned("Exists"), vec![Level::succ(Level::zero())]),
                        dom.ty(),
                    ),
                    Expr::lam(BinderInfo::Default, dom.ty(), body_expr),
                ),
            })
        }
    }
}

/// [`elaborate_goal_typed`] for the quantifier fragment: pre-parse, gate the
/// exact bindings against the clause's FREE variables (a quantifier-bound
/// variable is bound, so it must NOT appear in `var_types`), elaborate, and
/// ∀-close over the free variables exactly like the plain path.
fn elaborate_quantified_goal_typed(spec: &str, var_types: &[(&str, &str)]) -> Result<Expr, String> {
    let clause = parse_qclause(spec, true)?;
    elaborate_parsed_qclause_typed(&clause, var_types)
}

fn elaborate_parsed_qclause_typed(
    clause: &QClause,
    var_types: &[(&str, &str)],
) -> Result<Expr, String> {
    let mut free = Vec::new();
    collect_qclause_free_vars(clause, &mut Vec::new(), &mut free);
    let bindings = exact_typed_bindings(&free, var_types)?;
    let mut vars = free.clone();
    let mut var_domains = bindings;
    let body = elab_qclause(clause, &mut vars, 0, &mut var_domains)?;
    close_over_multi(&free, body, &var_domains)
}

// ---------------------------------------------------------------------------
// E6 — inferred facet certificates for definitional spec use of program fns.
//
// The v3 ruling (two-language design §3.1): NO surface marker. An ordinary
// Rust function can become usable *definitionally* in a spec only after
// Pure ∧ Total ∧ Deterministic ∧ NoPanic proofs and the exact function
// definition are bound into a sealed, item-bound, kernel-rechecked admission
// capability. Public facet findings alone are never sufficient. Upstream leaves
// spec-fn purity "expected but unenforced" (§1.2-1); Trust fails closed instead.
//
// This section is E6's diagnostic facet RECORD and QUERY path. The compiler
// populates it from conservative structural scans. These caller-constructible
// records are deliberately not authority: even four positive findings do not
// admit a call. The definitional import must eventually mint a private token
// bound to canonical item identity, program-semantics digest, kernel
// environment/proof identity, constant, and arity. No such production minting
// path exists today. The `Call`/
// `MethodCall` arms inside the elaborators stay as the unconditional
// fail-closed backstop, so no code path can elaborate a call by skipping
// the pre-pass.
//
// Facet provenance (the lanes that will populate this, per the banked
// series): NoPanic = the L0 whole-function aggregate; Total = the E5
// termination lane (decreases measures / structural recursion);
// Pure/Deterministic = the const-checker operations taxonomy (no interior
// mutability through params, no &mut params, floats excluded in v1).
// ---------------------------------------------------------------------------

/// Diagnostic status of one E6 facet of one program function.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FacetStatus {
    /// A conservative analysis established the facet; `evidence` names that
    /// analysis. This public value is a finding, not kernel-admission authority.
    Certified { evidence: String },
    /// No diagnostic finding either way — the fail-closed default.
    Unknown,
    /// An analysis lane ran and could not establish the facet; `reason`
    /// names the blocking construct (e.g. "back-edge present"). NOT a
    /// refutation — the property may hold, the lane just cannot see it.
    Undetermined { reason: String },
    /// Positively refuted (e.g. a reachable panic path); `reason` is shown
    /// verbatim in the diagnostic so the user learns *why*, not just "no".
    Refuted { reason: String },
}

/// Four diagnostic facet findings for one program function. `Certified` is the
/// legacy spelling of a positive finding; even four such values are not proof
/// objects and cannot authorize definitional spec use.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FnFacets {
    pub pure: FacetStatus,
    pub total: FacetStatus,
    pub deterministic: FacetStatus,
    pub no_panic: FacetStatus,
}

impl FnFacets {
    /// The fail-closed default: no positive findings.
    pub fn unknown() -> Self {
        FnFacets {
            pure: FacetStatus::Unknown,
            total: FacetStatus::Unknown,
            deterministic: FacetStatus::Unknown,
            no_panic: FacetStatus::Unknown,
        }
    }

    /// Build diagnostic statuses from a structural inference result. A `true`
    /// is recorded as `Certified { evidence }`; a `false` is `Undetermined`,
    /// not `Refuted`. Neither result can mint admission authority. This bare-
    /// boolean seam keeps `trust-spec-elab` independent of `trust-types`.
    pub fn from_structural_certificates(
        total: bool,
        no_panic: bool,
        pure: bool,
        deterministic: bool,
        evidence: &str,
    ) -> Self {
        let status = |ok: bool| {
            if ok {
                FacetStatus::Certified { evidence: evidence.to_string() }
            } else {
                FacetStatus::Undetermined {
                    reason: "no positive structural finding (may hold via a deeper lane)"
                        .to_string(),
                }
            }
        };
        FnFacets {
            pure: status(pure),
            total: status(total),
            deterministic: status(deterministic),
            no_panic: status(no_panic),
        }
    }

    /// All four facets carry certificates.
    pub fn admissible(&self) -> bool {
        self.facets().iter().all(|(_, s)| matches!(s, FacetStatus::Certified { .. }))
    }

    /// Human-readable status of every non-established facet, for diagnostics.
    pub fn deficits(&self) -> Vec<String> {
        self.facets()
            .iter()
            .filter_map(|(name, status)| match status {
                FacetStatus::Certified { .. } => None,
                FacetStatus::Unknown => {
                    Some(format!("{name} (not established: no diagnostic finding)"))
                }
                FacetStatus::Undetermined { reason } => {
                    Some(format!("{name} (not established: {reason})"))
                }
                FacetStatus::Refuted { reason } => Some(format!("{name} (refuted: {reason})")),
            })
            .collect()
    }

    fn facets(&self) -> [(&'static str, &FacetStatus); 4] {
        [
            ("Pure", &self.pure),
            ("Total", &self.total),
            ("Deterministic", &self.deterministic),
            ("NoPanic", &self.no_panic),
        ]
    }
}

/// E6 admission record (two-language design §3.1, brick 4): the Clean kernel
/// constant a program function has been ADMITTED as, for definitional use in a
/// spec. An admitted function's call `f(a, b)` elaborates to the kernel
/// constant applied to the elaborated arguments (`kernel_const a b`), because
/// the kernel now holds a re-checked defining equation for `f` (minted by the
/// white-box import from the MIR body — a later brick).
///
/// SOUNDNESS: an `Admission` is only ever *minted* by the kernel-import step
/// after all four facets are certified AND the kernel re-checks the definition;
/// carrying one in the table is not itself authority (see
/// [`FacetTable::admitted`], which additionally requires the facet record to be
/// [`FnFacets::admissible`]). Until the import brick lands, no `Admission` is
/// ever produced in the compiler, so every spec call still fails closed.
///
/// # I2 — the record says WHOSE authority
///
/// Before I2 a reflected Rust carrier and a kernel-re-checked Clean island
/// declaration were **indistinguishable** here: both were a `(kernel_const,
/// arity)` pair, and the only signal telling them apart was whether
/// `kernel_const` happened to start with `trust_import_`. A string prefix is an
/// audit procedure, not an invariant. The [`KernelStatus`] field is the
/// invariant.
///
/// The status is **private**, so an `Admission` cannot be assembled by struct
/// literal outside this crate: it is minted by whoever actually holds the
/// evidence, through [`Admission::reflected`] or [`Admission::kernel_checked`].
/// Neither constructor can *invent* a kernel verdict —
/// `KernelStatus::KernelChecked` is only constructible through
/// `trust_symbols`' sealed `KernelAuthority` seam, so
/// [`Admission::kernel_checked`] takes a status its caller already holds rather
/// than producing one.
///
/// # I3 — the record also says WHO MAY NAME IT
///
/// [`Admission::capability`] is the visibility half of the same idea. A
/// `KernelStatus` says how much the *kernel* vouches for the constant; a
/// [`trust_symbols::EffectiveCapability`] says whether naming it may produce a
/// value. The two are independent and both are needed: a `KernelChecked` Clean
/// `def` is maximally trusted and still may not emit a call, because §5(b) of
/// the decision doc withholds CALL by not minting a `DefId` for it, and
/// `CarrierEvidence::Total` — the other half of `SymbolHeader::grant_call` — is
/// unconstructed anywhere in this tree.
///
/// Like `status`, the field is **private**: an `Admission` cannot be assembled
/// by struct literal outside this crate, so a capability arrives from a
/// constructor that had a reason, and [`Admission::restrict`] can only ever
/// lower it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Admission {
    /// The Clean kernel constant name the function was admitted as.
    pub kernel_const: String,
    /// The function's arity (number of value parameters) — the elaborator
    /// applies the constant to exactly this many arguments.
    pub arity: usize,
    /// The CLAUSE-SIDE names of a mint whose parameter list is DERIVED
    /// (E6/E9 widening increment 7); `None` = no claim, never "agrees".
    pub param_names: Option<Vec<String>>,
    /// The constant's DECLARED Clean carriers (E6/E9 widening increment 8);
    /// a CHECK, never a source of typing. `None` = no record, fail-closed.
    pub carriers: Option<DeclaredCarriers>,
    /// How this constant got into the kernel environment, and on whose
    /// authority. Private: see the type docs.
    status: KernelStatus,
    /// I3: what a use site may do with it, after the transitive firewall.
    /// Private: see the type docs.
    capability: trust_symbols::EffectiveCapability,
    /// The proof-only symbol that bound the capability down, when
    /// [`Admission::restrict`] carried one. Diagnostics only.
    proof_only_via: Option<String>,
    /// The callee's RETURN domain, when the minting site recorded one (the
    /// compiler-side import reads it off the typed signature; the island
    /// admitter reads it off the kernel type's codomain). Private like the
    /// other evidence-bearing fields; the minting caller attaches it through
    /// [`Admission::with_return_domain`], and an absent domain simply leaves
    /// the pre-existing fail-closed default in force.
    ///
    /// **STEERING, plus one load-bearing use — read this before trusting the
    /// old sentence.** Until the nat-lift landed (2026-09-17) this field was
    /// pure steering: [`atom_domain`] used it to type a VARIABLE-FREE atom
    /// (`answer() == c42(0)`) at the callee's machine domain instead of the
    /// `Nat` default, and the comment here said "a wrongly recorded domain can
    /// only produce an ill-typed proposition the kernel then rejects — it can
    /// never make a false claim check".
    ///
    /// THAT IS NO LONGER TRUE FOR A LIFTED TERM. When a lift is decided from
    /// this field it selects an integer VALUE, not a literal range: `i128` and
    /// `u128` share the carrier `BitVec 128`, so recording the wrong one turns
    /// the same bit pattern into `-1` or into `2^128 - 1` and BOTH goals are
    /// well-typed. The kernel cannot catch it, so the field is now named in
    /// `docs/TCB.md`'s `EnsuresCitationDischarge` row and is read TWICE before
    /// any lift is built on it: the self function's recorded domain is
    /// cross-checked against the compiler's own resolved return type, and any
    /// other call may head a lifted term only when its carrier has a unique
    /// preimage (see [`TermPin`]). Outside a lift the old sentence still
    /// holds exactly.
    return_domain: Option<Domain>,
    /// Trust (ref-self I1): the name of the SEMANTIC VIEW this import was
    /// minted over, when it was not minted over the extracted body itself.
    ///
    /// Today the one value is `trust_types::e6_param_view::VIEW_MARKER`
    /// (`"frozen-shared-erased"`): the defining equation is a function of a
    /// frozen shared pointee's scalar field VALUES, and the correspondence
    /// between it and the Rust function rests on the aliasing assumption
    /// R1 names (`docs/TCB.md`).
    ///
    /// **This field exists to be DISCLOSED, not to be checked.** A row
    /// discharged against an admission carrying it is reported BELOW
    /// `Certified` and carries the marker on the spec-clean goal row, on the
    /// zero-authority denotation row and in the discharge note; on the JSON wire
    /// it takes a distinct solver label and ships no kernel proof evidence at
    /// all. `None` is the ordinary import and changes nothing about any existing
    /// lane.
    view: Option<String>,
    /// Trust (ref-self I1): when true, this admission may be named ONLY as the
    /// self-call [`elaborate_ensures`] splices in for `result` — never as an
    /// author-written call in any clause.
    ///
    /// Why a view import is not compositional. Its arity is the FLATTENED one
    /// (`x_ref(self.x, self.y)`), while Rust reads `x_ref` as taking one
    /// borrow, and rustc does not type-check clause text ([M-2] probes `v03`,
    /// `v04`). Without this mark `other_fn ensures result == x_ref(a, b)`
    /// would elaborate against a signature no Rust caller can write.
    ///
    /// It is also what makes "this goal rests on a view" decidable from the
    /// SELF function alone: no other view import can enter a goal, so the
    /// compiler's disclosure needs to look at exactly one admission.
    self_result_only: bool,
    /// Trust (GREEN THAT LIES, `docs/KNOWN_HAZARDS.md` 2026-09-18): the
    /// QUALIFICATION this row must travel with — one rendered disclosure
    /// sentence per `import` of the Clean island lane that Clean's built-in
    /// PRELUDE STAND-IN served instead of the library of that name.
    ///
    /// The declaration really was kernel-checked; what the sentence adds is
    /// *relative to what*. The compiler's per-island note says the same thing
    /// in the same words, but that note is per-ISLAND while this record is
    /// per-FUNCTION, so a consumer reading rows without the compilation's
    /// diagnostics saw an unqualified green. This field is how the green
    /// travels with its qualification.
    ///
    /// Rendered by the minting crate
    /// (`trust_certify::clean_island::CleanIslandStandinImport::disclosure`)
    /// and carried verbatim: this crate sits BELOW `trust-certify` in the
    /// dependency order, so it owns the obligation to keep the text attached
    /// to the row, never the wording.
    ///
    /// Empty is the honest default and the value for every admission that is
    /// not Clean-origin — a reflected Rust carrier has no island at all. It
    /// carries NO authority in either direction: nothing reads it to decide a
    /// verdict, and a row that gains a disclosure keeps exactly the strength
    /// it had.
    standin_disclosures: Vec<String>,
}

impl Admission {
    /// Mint the admission of a **reflected Rust carrier** (I2).
    ///
    /// This is what `admit_function_into` produces: the compiler projected a
    /// Rust `fn` into the Clean environment as `kernel_const`. The kernel
    /// checked that the carrier's body inhabits its declared type — `add_decl`
    /// is a full kernel check and a mistaken term is rejected, never admitted —
    /// but it did **not** re-check that `kernel_const` denotes that Rust `fn`.
    /// The compiler asserts that correspondence; it is TCB, and
    /// [`KernelStatus::Reflected`] is how the record says so.
    ///
    /// **I3 capability: CALL.** A reflected carrier denotes a Rust `fn` that
    /// already exists as compiled code, so naming it from a call position emits
    /// a call to something real. Rust's own resolver polices *whose* code may
    /// name it — that is CALL obeying the declaring language's ordinary
    /// visibility, symmetrically, and it is not this crate's to re-decide. What
    /// this crate must not do is hand CALL to a declaration that has no
    /// executable form at all, which is the Clean side.
    #[must_use]
    pub fn reflected(kernel_const: impl Into<String>, arity: usize) -> Self {
        Self {
            kernel_const: kernel_const.into(),
            arity,
            status: KernelStatus::Reflected,
            capability: trust_symbols::EffectiveCapability::Determined(
                trust_symbols::Capability::Call,
            ),
            param_names: None,
            carriers: None,
            proof_only_via: None,
            return_domain: None,
            view: None,
            self_result_only: false,
            standin_disclosures: Vec::new(),
        }
    }

    /// Mint the admission of a declaration the Clean CIC kernel re-checked.
    ///
    /// `status` must be a `KernelStatus::KernelChecked` the caller obtained
    /// from `trust_symbols`' sealed seam after a full certification audit. This
    /// constructor deliberately cannot build one: it only carries it. Passing a
    /// weaker status is *allowed* and is simply weaker — the enforcement in
    /// [`Admission::require_kernel_check`] fails closed on it.
    ///
    /// **I3 capability: PROOF.** This is a *Clean declaration*, and a Clean
    /// declaration has no executable form in this tree: CALL needs a total Rust
    /// carrier (`CarrierEvidence::Total`, which nothing constructs — I4) and a
    /// `DefId` (which `def_collector` does not mint — I5). Note the asymmetry
    /// with [`Admission::reflected`] and that it runs *opposite* to the kernel
    /// status: the more trusted declaration is the less executable one. That is
    /// correct and it is the whole point of two axes — trust and executability
    /// are different questions, and a design with one axis gets this backwards.
    #[must_use]
    pub fn kernel_checked(
        kernel_const: impl Into<String>,
        arity: usize,
        status: KernelStatus,
    ) -> Self {
        Self {
            kernel_const: kernel_const.into(),
            arity,
            status,
            capability: trust_symbols::EffectiveCapability::Determined(
                trust_symbols::Capability::Proof,
            ),
            param_names: None,
            carriers: None,
            proof_only_via: None,
            return_domain: None,
            view: None,
            self_result_only: false,
            standin_disclosures: Vec::new(),
        }
    }

    /// Attach the stand-in disclosures this row must be read relative to (see
    /// the field docs). REPLACES the recorded set rather than merging it: the
    /// minting site knows which island lane served this constant, and a caller
    /// that wants a union must compute it and pass the union — deciding that
    /// here would hide which of two callers was the more qualified one.
    ///
    /// Attaches no authority and removes none: the admission's status,
    /// capability, carriers and domains are untouched.
    #[must_use]
    pub fn with_standin_disclosures<I, S>(mut self, disclosures: I) -> Self
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        self.standin_disclosures = disclosures.into_iter().map(Into::into).collect();
        self
    }

    /// The stand-in disclosures recorded for this row, in the order the
    /// minting site supplied them. Empty means "no island `import` of this
    /// row's provenance was served by the prelude stand-in" — which is also
    /// what an admission that is not Clean-origin says.
    #[must_use]
    pub fn standin_disclosures(&self) -> &[String] {
        &self.standin_disclosures
    }

    /// Record the callee's declared RETURN domain (see the field docs). The
    /// four `admit_*` mints deliberately do not attach one — their caller is
    /// the party holding the typed signature or the kernel type, so the
    /// attachment happens where the evidence lives. Steering only: this
    /// grants no authority and widens no fragment; it only lets a
    /// variable-free clause atom be typed at the domain the constant already
    /// has.
    #[must_use]
    pub fn with_return_domain(mut self, domain: Domain) -> Self {
        self.return_domain = Some(domain);
        self
    }

    /// The recorded return domain, if the minting site attached one.
    #[must_use]
    pub fn return_domain(&self) -> Option<&Domain> {
        self.return_domain.as_ref()
    }

    /// How this constant entered the environment, and on whose authority.
    #[must_use]
    pub fn status(&self) -> &KernelStatus {
        &self.status
    }

    /// I3: what a use site may do with this constant, after the firewall.
    #[must_use]
    pub fn capability(&self) -> trust_symbols::EffectiveCapability {
        self.capability
    }

    /// I3: lower this admission's capability to the meet with `effective`,
    /// optionally naming the proof-only symbol that bound it.
    ///
    /// **Meet, never join.** There is deliberately no way to raise an
    /// admission's capability: this is the seam a
    /// [`trust_symbols::CapabilityClosure`] result is applied through, and a
    /// closure that could *promote* would let a producer's incomplete edge set
    /// manufacture executability. Applying the same closure twice, or applying
    /// two closures in either order, gives the same answer — which is what
    /// makes it safe to call from wherever the graph happens to be available.
    #[must_use]
    pub fn restrict(
        mut self,
        effective: trust_symbols::EffectiveCapability,
        via: Option<&str>,
    ) -> Self {
        let lowered = self.capability.meet(effective);
        if lowered != self.capability {
            self.proof_only_via = via.map(ToString::to_string);
        }
        self.capability = lowered;
        self
    }

    /// I3 enforcement: refuse this admission at a use site that needs more
    /// authority than it grants.
    ///
    /// `use_site` is the capability the *position* holds: PROOF for a spec
    /// clause or a `clean { … }` island, CALL for anything that will emit a
    /// call, a load, a const evaluation, a layout or dispatch decision, or
    /// discharge an unsafe obligation. `spelled` is how the source named it, so
    /// the refusal quotes the user's own text rather than a mangled constant.
    ///
    /// # Errors
    ///
    /// [`trust_symbols::ProofOnlyRefusal`] — "visible but not executable", with
    /// options. A PROOF use site never errors: §4.1.1 gives it total observer
    /// capability over every item-level declaration including private
    /// internals, same-crate and cross-crate, with zero annotations.
    pub fn require_at(
        &self,
        use_site: trust_symbols::Capability,
        spelled: &str,
    ) -> Result<(), trust_symbols::ProofOnlyRefusal> {
        use trust_symbols::{EffectiveCapability, ProofOnlyRefusal};
        if use_site.observes_at_least(self.capability.claimable()) {
            return Ok(());
        }
        Err(match (self.capability, self.proof_only_via.as_deref()) {
            (EffectiveCapability::Determined(_), Some(via)) => {
                ProofOnlyRefusal::Transitive { symbol: spelled.to_string(), via: via.to_string() }
            }
            (EffectiveCapability::Determined(_), None) => {
                ProofOnlyRefusal::Declared { symbol: spelled.to_string() }
            }
            // `EffectiveCapability::Unrecorded`, and — because the enum is
            // `#[non_exhaustive]` — any variant a later increment adds. A new
            // capability state this crate has never heard of is exactly the
            // "cannot determine" case, so it takes the same answer: refuse, and
            // say the closure is incomplete rather than assert a finding about
            // the symbol.
            _ => ProofOnlyRefusal::ClosureUnrecorded { symbol: spelled.to_string() },
        })
    }

    /// I2's enforcement: refuse this admission where a kernel re-check is
    /// required.
    ///
    /// # Errors
    ///
    /// [`trust_symbols::KernelCheckRequired`] when the admission is a reflected
    /// carrier (or anything else short of a kernel re-check). The error carries
    /// the fix with options.
    pub fn require_kernel_check(
        &self,
    ) -> Result<&trust_symbols::KernelVerdict, trust_symbols::KernelCheckRequired> {
        self.status.require_kernel_check(&self.kernel_const)
    }
}

#[derive(Debug, Clone, Default)]
struct FacetRecords {
    map: std::collections::BTreeMap<String, FnFacets>,
    /// E6 brick 4: the kernel constant each admitted function was minted as,
    /// keyed by the same callee path as `map`. Populated ONLY by the
    /// kernel-import step; empty until then, so admission never fires.
    admissions: std::collections::BTreeMap<String, Admission>,
}

/// Facet records keyed by the callee path exactly as spelled in the spec
/// (e.g. `min` or `cmp::min`). Method calls are NOT keyed here yet: method
/// resolution is receiver-type-dependent, so their keying arrives with the
/// compiler-side wiring that has typeck results in hand; until then method
/// calls keep the unconditional fail-closed diagnostic.
#[derive(Clone, Default)]
pub struct FacetTable {
    records: std::sync::Arc<FacetRecords>,
    /// I0 (ref-self design §4.0): the identifiers RUST BINDS in the clause
    /// scope of the one function whose clauses this table is about — every
    /// name bound by a parameter pattern, plus the const generics in scope —
    /// each mapped to the compiler-computed help line for the refusal.
    ///
    /// Why it cannot be derived here. The elaborator learns a parameter's
    /// existence only from the clause-side ROWS (`c.degree`, `c.coeff` for a
    /// by-value struct; nothing at all for a `&T`), so a BARE `c` looks like a
    /// free identifier and falls through to the admission table — where a
    /// `clean { def c … }` island definition of the same name answers. That is
    /// name capture: the clause says `c` and the goal says the island
    /// constant. Only the compiler knows the signature, so only the compiler
    /// can say which bare identifiers are Rust bindings; this field is how it
    /// says so, and an empty map (every non-compiler caller) reproduces the
    /// pre-I0 behaviour byte for byte.
    ///
    /// The map is a REFUSAL set, never a binding source: a name in it can only
    /// make an elaboration fail closed, never resolve.
    shadowed_idents: std::sync::Arc<std::collections::BTreeMap<String, String>>,
}

impl std::fmt::Debug for FacetTable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("FacetTable")
            .field("map", &self.records.map)
            .field("admissions", &self.records.admissions)
            .field("shadowed_idents", &*self.shadowed_idents)
            .finish()
    }
}

impl FacetTable {
    pub fn new() -> Self {
        Self::default()
    }

    /// Read every registered carrier recorded in this table, including call
    /// results and nested parameter carriers. This is passive transport input,
    /// not an admission query: even regressed/unused records are included, as
    /// they are in the environment-aware elaborator's revalidation pass.
    /// Consumers must revalidate each handle against their own environment.
    pub fn registered_carriers(&self) -> Vec<&RegisteredAdt> {
        fn collect<'a>(carrier: &'a Carrier, out: &mut Vec<&'a RegisteredAdt>) {
            match carrier {
                Carrier::RegisteredAdt(registered) => out.push(registered),
                Carrier::Option(inner) => collect(inner, out),
                _ => {}
            }
        }
        let mut result = Vec::new();
        for admission in self.records.admissions.values() {
            if let Some(Domain::RegisteredAdt(registered)) = admission.return_domain() {
                result.push(registered);
            }
            if let Some(carriers) = &admission.carriers {
                for carrier in carriers.params.iter().chain(std::iter::once(&carriers.ret)) {
                    collect(carrier, &mut result);
                }
            }
        }
        result
    }

    /// Build a table from a whole crate's STRUCTURAL facet inference in one call.
    /// Each entry is `(callee_path, total, no_panic, pure, deterministic)` — the
    /// four structural booleans in `(total, no_panic, pure, deterministic)`
    /// order. It records diagnostic findings only and cannot mint admission.
    pub fn from_structural_facets<I, S>(entries: I) -> Self
    where
        I: IntoIterator<Item = (S, bool, bool, bool, bool)>,
        S: Into<String>,
    {
        let mut table = Self::new();
        for (path, total, no_panic, pure, deterministic) in entries {
            table.insert(
                path,
                FnFacets::from_structural_certificates(
                    total,
                    no_panic,
                    pure,
                    deterministic,
                    "structural",
                ),
            );
        }
        table
    }

    pub fn insert(&mut self, callee_path: impl Into<String>, facets: FnFacets) {
        std::sync::Arc::make_mut(&mut self.records).map.insert(callee_path.into(), facets);
    }

    /// Monotonically upgrade existing records from a later whole-crate
    /// structural inference pass. Positive findings promote only an
    /// `Unknown`/`Undetermined` status; an existing certificate or refutation
    /// is never overwritten, and a missing record is never invented.
    pub fn upgrade_from_structural<I, S>(&mut self, entries: I)
    where
        I: IntoIterator<Item = (S, bool, bool, bool, bool)>,
        S: Into<String>,
    {
        fn promote(current: &FacetStatus, certified: bool) -> FacetStatus {
            match current {
                FacetStatus::Certified { .. } | FacetStatus::Refuted { .. } => current.clone(),
                FacetStatus::Unknown | FacetStatus::Undetermined { .. } if certified => {
                    FacetStatus::Certified { evidence: "structural+composition".to_string() }
                }
                FacetStatus::Unknown | FacetStatus::Undetermined { .. } => current.clone(),
            }
        }
        let records = std::sync::Arc::make_mut(&mut self.records);
        for (path, total, no_panic, pure, deterministic) in entries {
            let path = path.into();
            if let Some(existing) = records.map.get(&path) {
                let upgraded = FnFacets {
                    pure: promote(&existing.pure, pure),
                    total: promote(&existing.total, total),
                    deterministic: promote(&existing.deterministic, deterministic),
                    no_panic: promote(&existing.no_panic, no_panic),
                };
                records.map.insert(path, upgraded);
            }
        }
    }

    /// Remove a record (e.g. a bare-name key evicted as ambiguous). A missing
    /// key is fine — eviction must be idempotent. Also drops any admission for
    /// that key, so an evicted (ambiguous) name can never stay admitted.
    pub fn remove(&mut self, callee_path: &str) {
        let records = std::sync::Arc::make_mut(&mut self.records);
        records.map.remove(callee_path);
        records.admissions.remove(callee_path);
    }

    pub fn get(&self, callee_path: &str) -> Option<&FnFacets> {
        self.records.map.get(callee_path)
    }

    /// Record that `callee_path` has been ADMITTED as a Clean kernel constant
    /// (E6 brick 4). The caller is the kernel-import step, which mints the
    /// `Admission` only after the facets are certified and the kernel
    /// re-checks the definition. Recording it does NOT itself grant authority
    /// — [`Self::admitted`] still gates on [`FnFacets::admissible`].
    pub fn admit(&mut self, callee_path: impl Into<String>, admission: Admission) {
        std::sync::Arc::make_mut(&mut self.records)
            .admissions
            .insert(callee_path.into(), admission);
    }

    /// The kernel constant `callee_path` was admitted as, IFF it has a facet
    /// record that is [`FnFacets::admissible`] (all four facets certified) AND
    /// an admission has been minted for it. Both conditions are required: a
    /// stale admission whose facets later regressed, or an admission for a
    /// never-certified function, confers nothing (fail-closed). This is the
    /// query the elaborator's call arm consults to decide whether a spec call
    /// elaborates to the kernel constant or stays fail-closed.
    ///
    /// **I2, stated so the asymmetry is deliberate and not an oversight:** this
    /// query does NOT require [`Admission::require_kernel_check`]. A spec call
    /// site is precisely the position a reflected Rust carrier is *for* — the
    /// whole point of E6 kernel-import is that `f(x)` in an `ensures` clause
    /// denotes the imported defining equation of the Rust `fn f`. Requiring a
    /// kernel re-check here would refuse every program function and delete the
    /// lane. The positions that DO require one — where the compiler is about to
    /// report a Clean declaration the kernel authenticated — call
    /// `require_kernel_check` explicitly; see
    /// `trust_certify::clean_island::admit_certified_island_definition`.
    /// **Trust (ref-self I1), the ONE admission class that does not consult the
    /// record, stated so it is deliberate and not an oversight.** A
    /// [`Admission::is_self_result_only`] import was minted over a SEMANTIC
    /// VIEW of the function, not over its extracted body, and the view carries
    /// its OWN isolated facet certification, established at mint time
    /// (`trust_certify::clean_island::param_view`, gate V4). The record under
    /// this key describes the BORROW-BEARING body, which is deliberately NOT
    /// admissible — `facet_inference` refuses every `Ty::Ref` local — so
    /// requiring it would make every correctly minted view import fail closed,
    /// and the only way to satisfy it would be to write a certified record for
    /// a function whose body is not certified. That record would be a FALSE
    /// claim visible to every other consumer of this table (the citation
    /// sweep's per-facet status line reads it), so the mark is carried on the
    /// admission instead, where its scope is exactly the import it describes.
    ///
    /// This widens nothing: such an admission is refused at EVERY use site but
    /// the spliced self-call (see [`Admission::self_result_only`],
    /// [`ambient_call_admission`] and [`ambient_bare_admission`]).
    pub fn admitted(&self, callee_path: &str) -> Option<&Admission> {
        let admission = self.records.admissions.get(callee_path)?;
        if admission.is_self_result_only() {
            return Some(admission);
        }
        let certified = self.records.map.get(callee_path).is_some_and(FnFacets::admissible);
        if certified { Some(admission) } else { None }
    }

    /// I2: the status a **kernel constant** was minted under, looked up by the
    /// constant's own name rather than by the callee path.
    ///
    /// This is the reverse of [`Self::admitted`], and it exists because the
    /// consumer that must refuse a reflected carrier — the island-definition
    /// admitter — is handed a *kernel constant name*, not a Rust callee path.
    ///
    /// Deliberately **not** gated on [`FnFacets::admissible`]: this query is
    /// used to REFUSE, so a stale or facet-regressed admission must still be
    /// visible. Gating it would make a regressed record invisible and therefore
    /// silently acceptable, which is the wrong direction for a fail-closed
    /// check.
    ///
    /// A duplicate `kernel_const` under two callee paths is normal — the
    /// compiler records each admission under both the full def-path and the
    /// bare name — so the first match is answered; they are the same mint.
    #[must_use]
    pub fn kernel_const_status(&self, kernel_const: &str) -> Option<&KernelStatus> {
        self.records
            .admissions
            .values()
            .find(|admission| admission.kernel_const == kernel_const)
            .map(Admission::status)
    }

    /// Every callee path an admission is recorded under whose kernel constant
    /// is `kernel_const`, in key order — the def-path and each spec spelling
    /// the compiler recorded the same mint under.
    ///
    /// DIAGNOSTICS ONLY (E6 expansion I0): the E6 refusal text uses it to say
    /// that a function's import was not minted because its kernel name is
    /// already held by ANOTHER function's import (two def paths that mangle
    /// to one `trust_import_*` name; the kernel refuses the second with
    /// `DuplicateName`). Like [`Self::kernel_const_status`] it is deliberately
    /// not gated on the facet record, and nothing that decides consults it.
    #[must_use]
    pub fn admission_paths_for_kernel_const(&self, kernel_const: &str) -> Vec<&str> {
        self.records
            .admissions
            .iter()
            .filter(|(_, admission)| admission.kernel_const == kernel_const)
            .map(|(path, _)| path.as_str())
            .collect()
    }
    /// The kernel constant `callee_path` was admitted as, IFF it has a facet
    /// record that is [`FnFacets::admissible`] (all four facets certified) AND
    /// an admission has been minted for it. Both conditions are required: a
    /// stale admission whose facets later regressed, or an admission for a
    /// never-certified function, confers nothing (fail-closed). This is the
    /// query the elaborator's call arm consults to decide whether a spec call
    /// elaborates to the kernel constant or stays fail-closed.
    /// Whether an admission was MINTED for `callee_path`, regardless of its
    /// facet record. Only for diagnostics: [`Self::admitted`] is the query that
    /// decides anything, and it requires BOTH. Separating them is what tells a
    /// reader whether a mint never ran or ran and was then refused for its
    /// record -- a distinction "no import was minted" cannot express, and one
    /// that cost a full rebuild cycle to recover by hand.
    #[must_use]
    pub fn has_admission(&self, callee_path: &str) -> bool {
        self.records.admissions.contains_key(callee_path)
    }

    /// I0: install the identifiers Rust binds in the clause scope of the
    /// function whose clauses this table will elaborate (see
    /// [`FacetTable::shadowed_idents`]).
    ///
    /// The compiler calls this exactly once per clause, on the CLAUSE-LOCAL
    /// table it is about to hand the elaborator (`admit_clause_island_
    /// definitions`, the single admission seam of the four E9 consumers). An
    /// empty map is exactly the pre-I0 behaviour, so every other table
    /// construction is unchanged.
    pub fn set_shadowed_idents<I, K, V>(&mut self, idents: I)
    where
        I: IntoIterator<Item = (K, V)>,
        K: Into<String>,
        V: Into<String>,
    {
        self.shadowed_idents = std::sync::Arc::new(
            idents.into_iter().map(|(id, help)| (id.into(), help.into())).collect(),
        );
    }

    /// [`FacetTable::set_shadowed_idents`] as a builder, for tests and for
    /// callers that own the table.
    #[must_use]
    pub fn with_shadowed_idents<I, K, V>(mut self, idents: I) -> Self
    where
        I: IntoIterator<Item = (K, V)>,
        K: Into<String>,
        V: Into<String>,
    {
        self.set_shadowed_idents(idents);
        self
    }

    /// The help line recorded for `id` when a Rust binding of the specified
    /// function shadows it, else `None`.
    #[must_use]
    pub fn shadowed_ident(&self, id: &str) -> Option<&str> {
        self.shadowed_idents.get(id).map(String::as_str)
    }
}

/// Mint an E6 [`Admission`] for a CONSTANT function — a nullary function whose
/// body is a single machine-integer literal, e.g. `fn answer() -> u64 { 42 }` —
/// by importing its defining equation into the kernel. This is the minimal,
/// fully-sound slice of E6 kernel-import (two-language design §3.1, brick 4).
///
/// It builds the body term `<Carrier>.ofNat value` at the carrier type and
/// submits it as a `Declaration::Definition` via [`Environment::add_decl`], which
/// performs a FULL KERNEL CHECK that the value inhabits the type AND records the
/// defining equation `kernel_const ≡ value`. The `Admission` is minted ONLY if
/// the kernel accepts. SOUNDNESS: the kernel is the sole trust root — a mistaken
/// term is REJECTED, never admitted; an out-of-range literal fails closed BEFORE
/// the kernel (see [`Domain::numeral`]). This deliberately does NOT use
/// `add_skolem_axiom` / `add_constant_unchecked_for_test`, which would assert the
/// constant without a kernel-verified value (see the kernel-import spec note).
///
/// The caller (compiler-side) supplies `value`/`width` extracted from the
/// facet-certified `VerifiableFunction` body and is responsible for having
/// confirmed all four facets first; passing primitives keeps this free of a
/// `trust-types` dependency (mirroring [`FnFacets::from_structural_certificates`]).
/// Widening past constants (straight-line, then one `SwitchInt`) is the next
/// growth of the elaborator; see `docs/design-notes/2026-07-15-e6-kernel-import-spec.md`.
pub fn admit_constant_function(
    env: &mut Environment,
    kernel_const: &str,
    value: u64,
    width: MachineUIntWidth,
) -> Result<Admission, String> {
    let domain = Domain::Machine(width);
    let body = domain.numeral(u128::from(value))?; // range-checked, fails closed
    let ty = domain.ty(); // the carrier type, e.g. UInt64
    env.add_decl(Declaration::Definition {
        name: Name::from_string(kernel_const),
        level_params: vec![],
        type_: ty,
        value: body,
        is_reducible: true,
    })
    .map_err(|e| format!("kernel rejected the constant defining equation: {e:?}"))?;
    let carriers = DeclaredCarriers::of_domains(&[], &domain);
    Ok(Admission::reflected(kernel_const, 0)
        .with_declared_signature(Some(domain), Some(carriers)))
}

/// Mint an E6 [`Admission`] for a PROJECTION function — an n-ary function whose
/// body returns one of its parameters verbatim, e.g. `fn fst(x: u64, y: u64) ->
/// u64 { x }` or `fn id(x: u64) -> u64 { x }`. The next fragment beyond
/// [`admit_constant_function`]: it exercises the parametric machinery (lambda
/// binders + a function type) while staying fully sound.
///
/// The defining equation is `fun p0 … p_{n-1} => p_i` at type
/// `t0 → … → t_{n-1} → t_i`, submitted via [`Environment::add_decl`] (a FULL
/// KERNEL CHECK). Inside `n` nested lambdas the parameter at source position `i`
/// has de Bruijn index `n-1-i`. As with the constant case, the kernel is the
/// sole trust root — a mistaken term is rejected, never admitted — and the caller
/// (compiler-side) is responsible for having confirmed all four facets and that
/// `return_param` names a parameter whose type is the function's return type
/// (a projection can only return a same-typed parameter). Domains are passed as
/// primitives so this stays free of a `trust-types` dependency.
pub fn admit_projection_function(
    env: &mut Environment,
    kernel_const: &str,
    param_domains: &[Domain],
    return_param: usize,
) -> Result<Admission, String> {
    let n = param_domains.len();
    if n == 0 || return_param >= n {
        return Err(format!(
            "projection index {return_param} out of range for a {n}-parameter function"
        ));
    }
    // The return type is the projected parameter's carrier; the full type is the
    // arrow chain `t0 → … → t_{n-1} → t_i`.
    let ret_ty = param_domains[return_param].ty();
    let arrow_ty = param_domains.iter().rev().fold(ret_ty, |acc, d| Expr::arrow(d.ty(), acc));
    // Body `fun p0 … p_{n-1} => p_{return_param}`: under n binders the source
    // parameter `return_param` is de Bruijn index `n-1-return_param`.
    let body = Expr::bvar((n - 1 - return_param) as u32);
    let lam =
        param_domains.iter().rev().fold(body, |acc, d| Expr::lam(BinderInfo::Default, d.ty(), acc));
    env.add_decl(Declaration::Definition {
        name: Name::from_string(kernel_const),
        level_params: vec![],
        type_: arrow_ty,
        value: lam,
        is_reducible: true,
    })
    .map_err(|e| format!("kernel rejected the projection defining equation: {e:?}"))?;
    Ok(Admission::reflected(kernel_const, n)
        .with_declared_signature(Some(param_domains[return_param].clone()), Some(DeclaredCarriers::of_domains(param_domains, &param_domains[return_param]))))
}

/// Mint an E6 [`Admission`] for a FORWARDING function — an n-ary function whose
/// whole body is one call to an already-registered kernel constant with (some
/// of) its own parameters as the arguments, e.g. `fn pb_max_r(lhs: u64, rhs:
/// u64) -> u64 { pb_max(lhs, rhs) }` where `pb_max` is a kernel-checked Clean
/// island definition (joint Rust+Lean lane, 2026-09-15).
///
/// The defining equation is `fun p0 … p_{n-1} => callee p_{σ(0)} … p_{σ(m-1)}` at
/// type `t0 → … → t_{n-1} → ret`, where `σ = arg_params` maps each CALLEE
/// argument position to the SOURCE parameter that position receives — so a
/// body `f(rhs, lhs)` mints `callee p1 p0`, never a positional guess. Inside
/// `n` nested lambdas the source parameter `i` has de Bruijn index `n-1-i`.
///
/// SOUNDNESS. Two halves, neither of which is this function's to assert:
///
///  * that the Rust body IS that single forwarding call — the compiler-side
///    recognizer (`trust-certify`'s island-forwarding shape) establishes it
///    from the extracted MIR, exactly as every other `admit_*` mint relies on
///    its recognizer, and the status is `Reflected` (I2) for the same reason;
///  * that `callee` is the constant the Rust callee DENOTES — the compiler
///    writes that identity from its Clean-origin registry into the facet
///    table, and the recognizer reads it back through the table's
///    `KernelChecked` admission (never a name match).
///
/// What the kernel DOES check here, via [`Environment::add_decl`] (a full
/// kernel check): that `callee` applied to the chosen parameters at their
/// carriers inhabits `ret`. A carrier disagreement between the Rust signature
/// and the Clean declaration — a `u32` parameter forwarded into a `UInt64`
/// slot, a `bool` return over a `UInt64` body — is a type error and the mint
/// is refused, never admitted.
pub fn admit_forwarding_function(
    env: &mut Environment,
    kernel_const: &str,
    param_domains: &[Domain],
    callee_const: &str,
    arg_params: &[usize],
    ret_domain: &Domain,
) -> Result<Admission, String> {
    let n = param_domains.len();
    if callee_const.is_empty() {
        return Err("forwarding mint requires a named callee constant".to_string());
    }
    if callee_const == kernel_const {
        return Err(format!(
            "forwarding mint for `{kernel_const}` would forward to itself; a self-referential \
             defining equation is refused"
        ));
    }
    if let Some(bad) = arg_params.iter().find(|&&i| i >= n) {
        return Err(format!(
            "forwarding argument names source parameter {bad}, out of range for a \
             {n}-parameter function"
        ));
    }
    // Body `fun p0 … p_{n-1} => callee p_{σ(0)} … p_{σ(m-1)}`: each argument is
    // the bound variable of the source parameter it forwards.
    let head = Expr::const_(Name::from_string(callee_const), vec![]);
    let body = arg_params
        .iter()
        .fold(head, |acc, &i| Expr::app(acc, Expr::bvar((n - 1 - i) as u32)));
    let lam =
        param_domains.iter().rev().fold(body, |acc, d| Expr::lam(BinderInfo::Default, d.ty(), acc));
    let arrow_ty =
        param_domains.iter().rev().fold(ret_domain.ty(), |acc, d| Expr::arrow(d.ty(), acc));
    env.add_decl(Declaration::Definition {
        name: Name::from_string(kernel_const),
        level_params: vec![],
        type_: arrow_ty,
        value: lam,
        is_reducible: true,
    })
    .map_err(|e| format!("kernel rejected the forwarding defining equation: {e:?}"))?;
    Ok(Admission::reflected(kernel_const, n).with_declared_signature(
        Some(ret_domain.clone()),
        Some(DeclaredCarriers::of_domains(param_domains, ret_domain)),
    ))
}

/// Mint an E6 [`Admission`] for a single-domain ARITHMETIC function whose body is
/// an expression over its parameters — e.g. `fn winc(x: u64) -> u64 {
/// x.wrapping_add(1) }` (spelled `x + 1`, since the machine encoding is wrapping)
/// or `fn f(x, y) -> u64 { x + y }`. The third kernel-import fragment, and the
/// first with genuine OPERATIONS in the body.
///
/// It REUSES the tested elaboration path rather than re-encoding arithmetic:
/// [`elab_term`] builds the body term over the parameters (each machine op via the
/// exact `ofNat`/`toNat`/`Nat.*` wrapping encoding the certified monitors already
/// validate), [`close_over_lam_multi`] abstracts the parameters into lambdas, and
/// [`Environment::add_decl`] FULL-KERNEL-CHECKS the resulting
/// `fun p0 … p_{n-1} => <body>` at type `d → … → d`.
///
/// SOUNDNESS: `add_decl` guarantees well-typedness, but NOT that the term matches
/// the function's computation — so correctness rests on the elaboration encoding,
/// which is the same one the monitor tests concretely validate, and which the
/// caller-side test re-checks by definitional reduction (`is_def_eq`). Single
/// domain only (every parameter and the result share `domain`); a mixed-domain or
/// non-arithmetic body is out of this fragment and fails closed in `elab_term`.
/// The body syntax + parameter names come from the compiler-side extraction, so
/// this stays free of a `trust-types` dependency.
pub fn admit_expr_function(
    env: &mut Environment,
    kernel_const: &str,
    body: &str,
    param_names: &[&str],
    domain: &Domain,
) -> Result<Admission, String> {
    let syn: SynExpr = syn::parse_str(body).map_err(|e| format!("parse error: {e}"))?;
    let names: Vec<String> = param_names.iter().map(|s| (*s).to_string()).collect();
    // Single-domain by construction (every parameter and the result share
    // `domain`), so the per-variable map this mint elaborates under is the
    // uniform one — byte-identical to the pre-increment behaviour.
    let var_domains: std::collections::BTreeMap<String, Domain> =
        names.iter().map(|n| (n.clone(), domain.clone())).collect();
    let term = elab_term(&syn, &names, 0, &var_domains, domain)?;
    let lam = close_over_lam_multi(&names, term, &var_domains)?;
    let n = names.len();
    let arrow_ty = (0..n).fold(domain.ty(), |acc, _| Expr::arrow(domain.ty(), acc));
    env.add_decl(Declaration::Definition {
        name: Name::from_string(kernel_const),
        level_params: vec![],
        type_: arrow_ty,
        value: lam,
        is_reducible: true,
    })
    .map_err(|e| format!("kernel rejected the arithmetic defining equation: {e:?}"))?;
    Ok(Admission::reflected(kernel_const, n)
        .with_declared_signature(Some(domain.clone()), Some(DeclaredCarriers::of_domains(&vec![domain.clone(); n], domain))))
}

/// The comparison a [`admit_select_function`] branch tests.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SelectCmp {
    /// `<`
    Lt,
    /// `<=`
    Le,
    /// `==`
    Eq,
}

/// Mint an E6 [`Admission`] for a SELECT function — an n-ary function that
/// compares two of its parameters and returns one of them, i.e. the
/// `if <cmp> { p_then } else { p_else }` shape, of which `min2`/`max2` are the
/// canonical cases (`fn min2(a,b){ if a<b {a} else {b} }`). The conditional /
/// `SwitchInt` fragment, taken in its structured form so no `if`-expression
/// syntax parsing is needed — the compiler passes the comparison and the branch
/// parameter indices directly.
///
/// The body is `fun p0 … p_{n-1} => Bool.rec (fun _ => d) p_else p_then
/// <decision>`, where `<decision>` is the machine comparison decided through
/// `Nat.ble`/`Nat.beq` over `toNat` (`a<b` ≡ `!(b<=a)`), matching the certified
/// monitors' decision encoding. `Bool.rec` is the value-level if-then-else
/// eliminator (`Bool.rec motive false_case true_case scrutinee`). Single
/// machine (unsigned `uN`) or signed (`iN` — two's-complement `BitVec` with
/// the sign-flip order keys; see the `Domain::Signed` arm) domain; `add_decl`
/// FULL-KERNEL-CHECKS the result and a wrong construction is
/// caught by the caller's definitional-reduction (`is_def_eq`) test.
#[allow(clippy::too_many_arguments)]
pub fn admit_select_function(
    env: &mut Environment,
    kernel_const: &str,
    param_domains: &[Domain],
    cmp: SelectCmp,
    cmp_left: usize,
    cmp_right: usize,
    then_param: usize,
    else_param: usize,
) -> Result<Admission, String> {
    let n = param_domains.len();
    for &i in &[cmp_left, cmp_right, then_param, else_param] {
        if i >= n {
            return Err(format!("select index {i} out of range for a {n}-parameter function"));
        }
    }
    // The `ite` encoding constrains TWO pairs, not the whole signature: the
    // comparison's operands must share a domain (they are compared), and the
    // branches must share one (they are the two results, and that is the return
    // domain). Every OTHER parameter is just a binder and may have its own
    // carrier -- which is what lets a per-term rule step be minted at all,
    // since `sat_term(degree: i64, coeff: i64, lit: Lit)` flattens to a mixed
    // list and the old all-equal rule refused it outright.
    let cmp_domain = param_domains.get(cmp_left).ok_or("select comparison operand out of range")?;
    if param_domains.get(cmp_right) != Some(cmp_domain) {
        return Err("select compares operands of different domains".into());
    }
    let d = param_domains.get(then_param).ok_or("select branch out of range")?;
    if param_domains.get(else_param) != Some(d) {
        return Err("select branches have different domains".into());
    }
    // Exhaustive rather than `matches!`: a new carrier must state whether the
    // select mint's `ite` encoding is faithful for it, not inherit "yes" or
    // "no" from a wildcard.
    let carrier_ok = |dom: &Domain| match dom {
        Domain::Machine(_) | Domain::Signed(_) => true,
        Domain::Nat
        // A Rust BODY is never at `int`: the domain exists only as the
        // nat-lift codomain in a PROOF-position clause, and a mint that
        // accepted it would be minting an import for a value no Rust
        // expression has.
        | Domain::Int
        | Domain::U128
        | Domain::USize(_)
        | Domain::ISize(_)
        | Domain::Bool
        // The select mint's `ite` encoding has no reading over an Option
        // carrier (no order, no decidable comparison): fail closed.
        | Domain::OptionSigned(_)
        | Domain::RegisteredAdt(_) => false,
    };
    // Both the compared pair and the branch pair must be carriers the `ite`
    // encoding is faithful for; an unrelated binder's carrier is irrelevant.
    if !carrier_ok(d) || !carrier_ok(cmp_domain) {
        return Err("select currently requires a machine-integer or signed-integer domain".into());
    }
    // Under n binders the source parameter i is de Bruijn index n-1-i.
    // The indices were range-checked above; the closure restates `i < n` so
    // its own body is total (the verifier checks a closure on its own, with
    // `i` unconstrained, and refuted `n - 1 - i` at `i = n` — measured
    // 2026-09-13 on `dff2b22d1`).
    let bvar = |i: usize| -> Result<Expr, String> {
        if i >= n {
            return Err(format!("select index {i} out of range for a {n}-parameter function"));
        }
        Ok(Expr::bvar(de_bruijn_index(n, i, 0)?))
    };
    // Mint the term Clean's own `if _ then _ else _` elaborates to, so a user
    // writing `if a < b then a else b` produces a SYNTACTICALLY IDENTICAL term
    // and definitional equality closes the clause with nothing clever.
    //
    // The previous encoding was `Bool.rec` over `Nat.ble`-of-`toNat`. Both it
    // and the natural spelling are STUCK on a neutral scrutinee, but at
    // different recursors of different inductives — `Bool.rec` versus
    // `Decidable.rec` — so they compare structurally and never unify. That is
    // an iota mismatch, not an unfolding one: no amount of reducibility would
    // have bridged it. See docs/design/2026-07-25-select-encoding-ergonomics.md.
    //
    // SOUNDNESS: this delegates the MEANING of `<` to Clean's `instLT{carrier}`,
    // where the old encoding stated unsignedness explicitly via `toNat`. The
    // per-width `{carrier}.machine_agreement` theorem is what keeps that honest;
    // it is the load-bearing artifact now, not a nicety.
    let ty = d.ty();
    let one = Level::succ(Level::zero());
    let (l, r) = (bvar(cmp_left)?, bvar(cmp_right)?); // carrier level — NOT .toNat
    let (prop, inst) = decidable_comparison(cmp_domain, cmp, l, r)?;
    // ARGUMENT ORDER: `ite α c h t e` takes THEN fourth and ELSE fifth, the
    // opposite of `Bool.rec`, which took ELSE first. Reversing these silently
    // mints `max` where the program wrote `min`, and the E9 goal still closes
    // whenever the island happens to be reversed the same way — so a positive
    // fixture alone does NOT catch it. The paired NEG probe is the net.
    let body = Expr::apps(
        Expr::const_(Name::from_string("ite"), vec![one]),
        [ty.clone(), prop, inst, bvar(then_param)?, bvar(else_param)?],
    );
    // Bind each parameter at ITS OWN carrier, and return the branch carrier --
    // the same per-parameter shape `admit_projection_function` builds. Folding
    // one carrier over every binder is what made a mixed signature impossible.
    let lam = param_domains
        .iter()
        .rev()
        .fold(body, |acc, pd| Expr::lam(BinderInfo::Default, pd.ty(), acc));
    let arrow_ty =
        param_domains.iter().rev().fold(d.ty(), |acc, pd| Expr::arrow(pd.ty(), acc));
    env.add_decl(Declaration::Definition {
        name: Name::from_string(kernel_const),
        level_params: vec![],
        type_: arrow_ty,
        value: lam,
        is_reducible: true,
    })
    .map_err(|e| format!("kernel rejected the select defining equation: {e:?}"))?;
    Ok(Admission::reflected(kernel_const, n)
        .with_declared_signature(Some(d.clone()), Some(DeclaredCarriers::of_domains(param_domains, d))))
}

/// Mint an E6 [`Admission`] for a SELECT-vs-LITERAL function (R2/C9) — an
/// n-ary function that compares one of its parameters against a
/// machine-integer LITERAL and returns one of its parameters, i.e. the
/// `if p_cmp ⊲ LIT { p_then } else { p_else }` shape, of which the threshold
/// select `fn min10(a, b) { if a < 10 { a } else { b } }` and gcd's guard
/// `if b == 0 { a } else { … }` are the canonical cases.
///
/// A **NEW admit route**, deliberately: `fragment_widening_probes.rs`
/// (probe_i, 2026-08-21) measured that NO existing producer could mint this
/// side B — [`admit_select_function`] compares two PARAMETERS by signature
/// (a literal operand is unrepresentable in its input vocabulary, not merely
/// refused), and [`admit_expr_function`]'s term fragment has no
/// `if`/comparison. Rather than widen a frozen producer, this function is
/// added BESIDE the four existing `admit_*`, which are untouched.
///
/// The term construction mirrors [`admit_select_function`]'s exactly — the
/// `ite` tree Clean's own `elab_if` mints (the 2026-07-25 Option-B ruling),
/// so a user writing `if a < 10 then a else b` produces the same tree shape
/// and definitional equality closes with nothing clever — with ONE
/// difference: the comparison's RIGHT operand is the literal's numeral term
/// ([`Domain::numeral`], range-checked, fails closed) instead of a bound
/// parameter. The literal is STRICTLY the right operand: a literal on the
/// left (`if 10 < a`) is unrepresentable in this signature, the same
/// fail-closed-by-vocabulary rule the parameter version applies to literals.
/// The numeral is minted in the CARRIER spelling (`{C}.ofNat n`); the kernel
/// identifying it with the surface `OfNat.ofNat` spelling a real island
/// elaborates is a MEASURED fact (the a4–a6 arithmetic probes first, and
/// probe_i's own both-spelling ADMIT for this shape), never an assumption.
///
/// Single machine domain over ALL parameters, as for every arithmetic
/// reflection; `add_decl` FULL-KERNEL-CHECKS the result, and a wrong
/// construction is caught by the caller's definitional-reduction
/// (`is_def_eq`) test.
#[allow(clippy::too_many_arguments)]
pub fn admit_select_literal_function(
    env: &mut Environment,
    kernel_const: &str,
    param_domains: &[Domain],
    cmp: SelectCmp,
    cmp_param: usize,
    literal: u128,
    then_param: usize,
    else_param: usize,
) -> Result<Admission, String> {
    let n = param_domains.len();
    for &i in &[cmp_param, then_param, else_param] {
        if i >= n {
            return Err(format!("select index {i} out of range for a {n}-parameter function"));
        }
    }
    let d = param_domains.first().ok_or("select needs at least one parameter")?;
    if !param_domains.iter().all(|x| x == d) {
        return Err("select over mixed parameter domains is unsupported".into());
    }
    let width = match d {
        Domain::Machine(w) => *w,
        _ => return Err("select currently requires a machine-integer domain".into()),
    };
    let carrier = width.carrier();
    // Under n binders the source parameter i is de Bruijn index n-1-i.
    // The indices were range-checked above; the closure restates `i < n` so
    // its own body is total (the verifier checks a closure on its own, with
    // `i` unconstrained, and refuted `n - 1 - i` at `i = n` — measured
    // 2026-09-13 on `dff2b22d1`).
    let bvar = |i: usize| -> Result<Expr, String> {
        if i >= n {
            return Err(format!("select index {i} out of range for a {n}-parameter function"));
        }
        Ok(Expr::bvar(de_bruijn_index(n, i, 0)?))
    };
    let ty = d.ty();
    let zero = Level::zero();
    let one = Level::succ(Level::zero());
    // The comparison's operands: the parameter on the LEFT, the range-checked
    // numeral on the RIGHT. `Domain::numeral` fails closed on an out-of-range
    // literal BEFORE the kernel, exactly as in `admit_constant_function`.
    let (l, r) = (bvar(cmp_param)?, d.numeral(literal)?);
    let inst_c = |s: &str| Expr::const_(Name::from_string(s), vec![]);
    let (prop, inst) = match cmp {
        SelectCmp::Lt => (
            Expr::apps(
                Expr::const_(Name::from_string("LT.lt"), vec![zero.clone()]),
                [ty.clone(), inst_c(width.inst_lt_const()), l.clone(), r.clone()],
            ),
            // R2/C9 SPELLING-GAP FIX (measured 2026-08-21): the REAL island
            // elaborator resolves a literal comparison's decidability by
            // REDUCTION TO NAT — `instDecidableNatLt` over the parameter's
            // `toNat` projection chain (`Proj Fin 0 (Proj BitVec 0 (Proj {C}
            // 0 x))`) and the BARE Nat literal — never the carrier instance
            // this arm used to mint. Kernel defeq is INTENSIONAL on the
            // stuck `ite` (the C5.0 finding), so the two instance spellings
            // can never identify; minting what `elab_if` elaborates is the
            // same Option-B ruling `admit_select_function` was built on
            // (2026-07-25), now applied where the measurement demanded it.
            {
                let bare_nat = u64::try_from(literal)
                    .map_err(|_| format!("select literal {literal} exceeds u64"))?;
                Expr::apps(
                    inst_c("instDecidableNatLt"),
                    [
                        Expr::proj(
                            Name::from_string("Fin"),
                            0,
                            Expr::proj(
                                Name::from_string("BitVec"),
                                0,
                                Expr::proj(Name::from_string(carrier), 0, bvar(cmp_param)?),
                            ),
                        ),
                        Expr::nat_lit(bare_nat),
                    ],
                )
            },
        ),
        SelectCmp::Le => (
            Expr::apps(
                Expr::const_(Name::from_string("LE.le"), vec![zero.clone()]),
                [ty.clone(), inst_c(width.inst_le_const()), l.clone(), r.clone()],
            ),
            Expr::apps(inst_c(width.inst_decidable_le_const()), [l, r]),
        ),
        SelectCmp::Eq => (
            Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![one.clone()]),
                [ty.clone(), l.clone(), r.clone()],
            ),
            Expr::apps(inst_c(width.inst_decidable_eq_const()), [l, r]),
        ),
    };
    // ARGUMENT ORDER: `ite α c h t e` takes THEN fourth and ELSE fifth — the
    // same polarity trap `admit_select_function` documents; the paired
    // mutation probes are the net here too.
    let body = Expr::apps(
        Expr::const_(Name::from_string("ite"), vec![one]),
        [ty.clone(), prop, inst, bvar(then_param)?, bvar(else_param)?],
    );
    let lam = (0..n).fold(body, |acc, _| Expr::lam(BinderInfo::Default, d.ty(), acc));
    let arrow_ty = (0..n).fold(d.ty(), |acc, _| Expr::arrow(d.ty(), acc));
    env.add_decl(Declaration::Definition {
        name: Name::from_string(kernel_const),
        level_params: vec![],
        type_: arrow_ty,
        value: lam,
        is_reducible: true,
    })
    .map_err(|e| format!("kernel rejected the select-literal defining equation: {e:?}"))?;
    // I2: reflected carrier — see `admit_constant_function`.
    Ok(Admission::reflected(kernel_const, n))
}

/// One operand position of a [`admit_select_operands_function`] select: a
/// source parameter, or an in-range machine numeral.
///
/// **The vocabulary is the position's, not the shape's** — the same operand
/// type serves the comparison's right-hand side and BOTH arms, so "a numeral
/// may stand where a parameter may stand" is one statement in one place rather
/// than a per-position rule. That is what makes the route GENERAL: it was not
/// widened to admit a particular body, it was stated over the operand
/// vocabulary the `ite` tree already has.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SelectOperand {
    /// A 0-based source parameter.
    Param(usize),
    /// An in-range machine numeral, minted in the CARRIER spelling
    /// (`{C}.ofNat n`) by [`Domain::numeral`], which range-checks it and fails
    /// closed BEFORE the kernel.
    Literal(u128),
}

/// Mint an E6 [`Admission`] for a GENERAL SELECT function (§6f landing 3) —
/// an n-ary function that compares a parameter against a parameter or a
/// numeral and returns, in each arm, a parameter **or a numeral**:
/// `if p_l ⊲ <rhs> then <then> else <else>`, of which `fn clampz(a, b) { if a
/// < b { a } else { 0 } }` and `fn nz(a) { if a < 1 { 0 } else { a } }` are
/// canonical.
///
/// A **NEW admit route**, added BESIDE [`admit_select_function`] and
/// [`admit_select_literal_function`], which are untouched — the same
/// discipline R2/C9 applied when the literal comparison operand turned out to
/// be unrepresentable in a frozen producer's signature. The two frozen routes
/// are the special case "every arm is a parameter", and
/// `trust-clean-origin/tests/landing3_selection_probes.rs::l3_p4` is the
/// standing control that this route reproduces BOTH of their terms EXACTLY on
/// that overlap, at every comparison, every width and every index assignment
/// it measures. That control is why generalizing here does not silently become
/// a second, drifting builder of one term: the two constructions stay separate
/// and are measured equal.
///
/// # What is deliberately NOT generalized, and why it is a measurement
///
/// * **The comparison's LEFT operand stays a parameter.** Not out of caution:
///   `if 10 < a then …` does not ELABORATE in the real Clean island at all
///   (measured, `l3_p6` — the bare numeral is typed `Nat` and the comparison
///   is a type mismatch), so a producer able to spell it would be capability
///   nothing can reach.
/// * **A COMPUTED operand (`a + 1 < b`) stays out.** It elaborates, but the
///   real elaborator resolves its decidability by NORMALIZING the modular
///   reduction into a `Nat.rec`-headed term (measured, `l3_p5`). Side B would
///   have to reproduce an elaborator normal form, which is not an operand
///   vocabulary question at all.
///
/// The term construction mirrors the two frozen routes exactly — the `ite`
/// tree Clean's own `elab_if` mints (the 2026-07-25 Option-B ruling) — with
/// the comparison's instance chosen by the RIGHT operand's form, because the
/// real elaborator chooses it that way: a parameter comparison resolves at the
/// carrier instance (`instDecidable{C}Lt`), and a literal comparison at `<`
/// resolves by REDUCTION TO NAT (`instDecidableNatLt` over the parameter's
/// `toNat` projection chain — the R2/C9 spelling-gap finding). `add_decl`
/// FULL-KERNEL-CHECKS the result; the arms are ordinary `ite` arguments, so a
/// wrong arm is a wrong term the caller's definitional-reduction test refuses.
#[allow(clippy::too_many_arguments)]
pub fn admit_select_operands_function(
    env: &mut Environment,
    kernel_const: &str,
    param_domains: &[Domain],
    cmp: SelectCmp,
    cmp_left: usize,
    cmp_right: SelectOperand,
    then_arm: SelectOperand,
    else_arm: SelectOperand,
) -> Result<Admission, String> {
    let n = param_domains.len();
    if cmp_left >= n {
        return Err(format!("select index {cmp_left} out of range for a {n}-parameter function"));
    }
    for operand in [cmp_right, then_arm, else_arm] {
        if let SelectOperand::Param(index) = operand {
            if index >= n {
                return Err(format!("select index {index} out of range for a {n}-parameter function"));
            }
        }
    }
    let d = param_domains.first().ok_or("select needs at least one parameter")?;
    if !param_domains.iter().all(|x| x == d) {
        return Err("select over mixed parameter domains is unsupported".into());
    }
    let width = match d {
        Domain::Machine(w) => *w,
        _ => return Err("select currently requires a machine-integer domain".into()),
    };
    let carrier = width.carrier();
    // Under n binders the source parameter i is de Bruijn index n-1-i.
    // The indices were range-checked above; the closure restates `i < n` so
    // its own body is total (the verifier checks a closure on its own, with
    // `i` unconstrained, and refuted `n - 1 - i` at `i = n` — measured
    // 2026-09-13 on `dff2b22d1`).
    let bvar = |i: usize| -> Result<Expr, String> {
        if i >= n {
            return Err(format!("select index {i} out of range for a {n}-parameter function"));
        }
        Ok(Expr::bvar(de_bruijn_index(n, i, 0)?))
    };
    // ONE operand renderer for every position — the comparison's right-hand
    // side and both arms. A numeral is minted by `Domain::numeral`, which
    // range-checks it and fails closed before the kernel; that is also the
    // spelling (`{C}.ofNat v`) the real island elaborates a constant arm to.
    let operand = |o: SelectOperand| -> Result<Expr, String> {
        match o {
            SelectOperand::Param(index) => bvar(index),
            SelectOperand::Literal(value) => d.numeral(value),
        }
    };
    let ty = d.ty();
    let zero = Level::zero();
    let one = Level::succ(Level::zero());
    let l = bvar(cmp_left)?;
    let r = operand(cmp_right)?;
    let inst_c = |s: &str| Expr::const_(Name::from_string(s), vec![]);
    let (prop, inst) = match (cmp, cmp_right) {
        // The literal comparison at `<`: the REAL elaborator's Nat-reduced
        // instance, identical to `admit_select_literal_function`'s arm. Only
        // `<` is measured through the real island path; `<=`/`==` against a
        // literal keep the carrier instance the frozen route mints, so this
        // route and that one agree everywhere they overlap.
        (SelectCmp::Lt, SelectOperand::Literal(value)) => (
            Expr::apps(
                Expr::const_(Name::from_string("LT.lt"), vec![zero.clone()]),
                [ty.clone(), inst_c(width.inst_lt_const()), l.clone(), r.clone()],
            ),
            {
                let bare_nat = u64::try_from(value)
                    .map_err(|_| format!("select literal {value} exceeds u64"))?;
                Expr::apps(
                    inst_c("instDecidableNatLt"),
                    [
                        Expr::proj(
                            Name::from_string("Fin"),
                            0,
                            Expr::proj(
                                Name::from_string("BitVec"),
                                0,
                                Expr::proj(Name::from_string(carrier), 0, bvar(cmp_left)?),
                            ),
                        ),
                        Expr::nat_lit(bare_nat),
                    ],
                )
            },
        ),
        (SelectCmp::Lt, SelectOperand::Param(_)) => (
            Expr::apps(
                Expr::const_(Name::from_string("LT.lt"), vec![zero.clone()]),
                [ty.clone(), inst_c(width.inst_lt_const()), l.clone(), r.clone()],
            ),
            Expr::apps(inst_c(width.inst_decidable_lt_const()), [l, r]),
        ),
        (SelectCmp::Le, _) => (
            Expr::apps(
                Expr::const_(Name::from_string("LE.le"), vec![zero.clone()]),
                [ty.clone(), inst_c(width.inst_le_const()), l.clone(), r.clone()],
            ),
            Expr::apps(inst_c(width.inst_decidable_le_const()), [l, r]),
        ),
        (SelectCmp::Eq, _) => (
            Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![one.clone()]),
                [ty.clone(), l.clone(), r.clone()],
            ),
            Expr::apps(inst_c(width.inst_decidable_eq_const()), [l, r]),
        ),
    };
    // ARGUMENT ORDER: `ite α c h t e` takes THEN fourth and ELSE fifth — the
    // same polarity trap both frozen routes document, and the reason
    // `control_10`'s swapped-arm half exists.
    let body = Expr::apps(
        Expr::const_(Name::from_string("ite"), vec![one]),
        [ty.clone(), prop, inst, operand(then_arm)?, operand(else_arm)?],
    );
    let lam = (0..n).fold(body, |acc, _| Expr::lam(BinderInfo::Default, d.ty(), acc));
    let arrow_ty = (0..n).fold(d.ty(), |acc, _| Expr::arrow(d.ty(), acc));
    env.add_decl(Declaration::Definition {
        name: Name::from_string(kernel_const),
        level_params: vec![],
        type_: arrow_ty,
        value: lam,
        is_reducible: true,
    })
    .map_err(|e| format!("kernel rejected the general-select defining equation: {e:?}"))?;
    // I2: reflected carrier — see `admit_constant_function`.
    Ok(Admission::reflected(kernel_const, n))
}

/// Mint an E6 [`Admission`] for a **`BEq`-CONDITIONED SELECT** (§6f landing 5)
/// — the select a user writes with the idiomatic `==` rather than the
/// propositional `=`:
///
/// ```text
/// def eqbeq (a b : UInt64) : UInt64 := if a == b then a else b
/// ```
///
/// A **NEW admit route**, added BESIDE [`admit_select_function`],
/// [`admit_select_literal_function`] and [`admit_select_operands_function`],
/// all three of which are untouched — the discipline R2/C9 established when
/// the literal comparison operand turned out to be unrepresentable in a frozen
/// producer's signature, and §6f landing 3 repeated for the operand arms.
///
/// # Why it is a route and not a `SelectCmp` variant
///
/// `==` is **not a fourth comparison**. It is a SECOND SPELLING of the
/// equality one, and the difference is a whole layer rather than an operator:
/// [`SelectCmp::Eq`] states the condition as the PROPOSITION `Eq {C} l r`,
/// while `==` states it as a **`Bool`-level decision lifted back to a
/// proposition**. Measured on the real island elaborator at every machine
/// width (`trust-clean-origin/tests/landing5_selection_probes.rs::l5_p1`),
/// `if a == b then a else b` elaborates to
///
/// ```text
/// ite.{1} {C}
///   (Eq.{1} Bool (BEq.beq.{0} {C} (instBEqOfDecidableEq.{0} {C} instDecidableEq{C}) l r)
///                Bool.true)
///   (instDecidableEqBool (BEq.beq.{0} {C} (instBEqOfDecidableEq.{0} {C} instDecidableEq{C}) l r)
///                        Bool.true)
///   then else
/// ```
///
/// Adding a `SelectCmp` variant would have forced an arm into the two frozen
/// producers' exhaustive `match cmp`, which is exactly the edit R2/C9 refused
/// to make; and the two spellings are NOT definitionally equal — the kernel
/// says so in its own words, since the island cannot even close
/// `theorem … : (if a == b then a else b) = (if a = b then a else b) := rfl`
/// (measured, `l5_p3`). So this is a real second term, not a rendering choice.
///
/// # The instance is UNIFORM across the operand vocabulary
///
/// The decidability instance is `instDecidableEqBool <decision> Bool.true` for
/// EVERY operand vocabulary — parameter-vs-parameter and parameter-vs-numeral
/// alike — because the decision is resolved at `Bool`, where both operands are
/// already `Bool`, one layer above the carrier. That is measured
/// (`l5_p1`), and it is the one respect in which this route is SIMPLER than
/// [`admit_select_operands_function`], whose `<`-against-a-literal arm has to
/// mint the elaborator's Nat-reduced instance (the R2/C9 spelling-gap
/// finding). One spelling, no per-operand arm.
///
/// # What it deliberately does NOT cover
///
/// * **`!=`.** Measured (`l5_p7`): `a != b` elaborates to the same tree with a
///   `Bool.not` wrapped around the decision. That is a third spelling with no
///   MIR realization on the emit lane (`SelectCmp` has no `Ne`), and admitting
///   the negation here would let a caller mint a term whose emitted diamond
///   would have to branch the other way — the polarity trap, one layer up. It
///   is a separate demand in the ledger, not a flag on this route.
/// * **A numeral on the comparison's LEFT**, for the reason `l3_p6` measured
///   for every other select route: the shape does not elaborate at all.
///
/// `add_decl` FULL-KERNEL-CHECKS the result; the arms are ordinary `ite`
/// arguments, so a wrong arm is a wrong term the caller's definitional-
/// reduction test refuses.
#[allow(clippy::too_many_arguments)]
pub fn admit_select_beq_function(
    env: &mut Environment,
    kernel_const: &str,
    param_domains: &[Domain],
    cmp_left: usize,
    cmp_right: SelectOperand,
    then_arm: SelectOperand,
    else_arm: SelectOperand,
) -> Result<Admission, String> {
    let n = param_domains.len();
    if cmp_left >= n {
        return Err(format!("select index {cmp_left} out of range for a {n}-parameter function"));
    }
    for operand in [cmp_right, then_arm, else_arm] {
        if let SelectOperand::Param(index) = operand {
            if index >= n {
                return Err(format!("select index {index} out of range for a {n}-parameter function"));
            }
        }
    }
    let d = param_domains.first().ok_or("select needs at least one parameter")?;
    if !param_domains.iter().all(|x| x == d) {
        return Err("select over mixed parameter domains is unsupported".into());
    }
    let width = match d {
        Domain::Machine(w) => *w,
        _ => return Err("select currently requires a machine-integer domain".into()),
    };
    // Under n binders the source parameter i is de Bruijn index n-1-i.
    // The indices were range-checked above; the closure restates `i < n` so
    // its own body is total (the verifier checks a closure on its own, with
    // `i` unconstrained, and refuted `n - 1 - i` at `i = n` — measured
    // 2026-09-13 on `dff2b22d1`).
    let bvar = |i: usize| -> Result<Expr, String> {
        if i >= n {
            return Err(format!("select index {i} out of range for a {n}-parameter function"));
        }
        Ok(Expr::bvar(de_bruijn_index(n, i, 0)?))
    };
    // ONE operand renderer for every position, exactly as the general select
    // route states it: a numeral is minted by `Domain::numeral`, which
    // range-checks it and fails closed before the kernel, and which is the
    // spelling (`{C}.ofNat v`) the real island elaborates a constant operand
    // to in this tree as well (measured, `l5_p1`).
    let operand = |o: SelectOperand| -> Result<Expr, String> {
        match o {
            SelectOperand::Param(index) => bvar(index),
            SelectOperand::Literal(value) => d.numeral(value),
        }
    };
    let ty = d.ty();
    let zero = Level::zero();
    let one = Level::succ(Level::zero());
    let inst_c = |s: &str| Expr::const_(Name::from_string(s), vec![]);
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
    let bool_true = Expr::const_(Name::from_string("Bool.true"), vec![]);
    // The `Bool`-level DECISION. It appears TWICE in the elaborated tree — in
    // the proposition and inside the instance — and it is built ONCE here for
    // that reason: two constructions of one subterm are two places a spelling
    // can drift, and the kernel compares the instance's operands against the
    // proposition's.
    let decision = Expr::apps(
        Expr::const_(Name::from_string("BEq.beq"), vec![zero.clone()]),
        [
            ty.clone(),
            Expr::apps(
                Expr::const_(Name::from_string("instBEqOfDecidableEq"), vec![zero]),
                [ty.clone(), inst_c(width.inst_decidable_eq_const())],
            ),
            bvar(cmp_left)?,
            operand(cmp_right)?,
        ],
    );
    // The lift: a `Bool` decision becomes a proposition by `= true`. The
    // SCRUTINEE is `Bool.true` and nothing else — `Bool.false` here would mint
    // the complementary function while every arm, index and width stayed
    // right, which is why `l5_p4` refuses that mutant explicitly.
    let prop = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![one.clone()]),
        [bool_ty, decision.clone(), bool_true.clone()],
    );
    let inst = Expr::apps(inst_c("instDecidableEqBool"), [decision, bool_true]);
    // ARGUMENT ORDER: `ite α c h t e` takes THEN fourth and ELSE fifth — the
    // same polarity trap all three sibling routes document.
    let body = Expr::apps(
        Expr::const_(Name::from_string("ite"), vec![one]),
        [ty.clone(), prop, inst, operand(then_arm)?, operand(else_arm)?],
    );
    let lam = (0..n).fold(body, |acc, _| Expr::lam(BinderInfo::Default, d.ty(), acc));
    let arrow_ty = (0..n).fold(d.ty(), |acc, _| Expr::arrow(d.ty(), acc));
    env.add_decl(Declaration::Definition {
        name: Name::from_string(kernel_const),
        level_params: vec![],
        type_: arrow_ty,
        value: lam,
        is_reducible: true,
    })
    .map_err(|e| format!("kernel rejected the `==`-select defining equation: {e:?}"))?;
    // I2: reflected carrier — see `admit_constant_function`.
    Ok(Admission::reflected(kernel_const, n))
}

/// **§6f LANDING 8** — one DECISION operand of
/// [`admit_select_beq_operands_function`].
///
/// [`SelectOperand`]'s two leaves, plus a COMPUTED operand carried as a SURFACE
/// RENDERING rather than as a term.
///
/// # The rendering is the point, not a shortcut
///
/// A `Computed` operand's `Expr` is built by [`elab_term`] — the FROZEN
/// elaborator this crate has used for the Rust→Clean direction since long
/// before the Clean-origin lane existed, and the same one `admit_expr_function`
/// calls for a whole-body `p0 & 1`. So the computed subterm rides frozen-R's
/// pedigree exactly as §6f landing 7's four raw-binop rows do, and this route
/// authors no new arithmetic encoding at all: it authors the `ite` frame around
/// one, which is what its three sibling select routes already do.
///
/// The de Bruijn convention matches by construction rather than by agreement:
/// `elab_term(_, vars, 0, _)` gives a variable at position `i` the index
/// `vars.len() - 1 - i`, which is the same `bvar(i)` the surrounding frame
/// uses. There is no re-indexing step, and therefore no place one could be
/// wrong.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SelectBeqOperand {
    /// A 0-based source parameter.
    Param(usize),
    /// An in-range machine numeral, minted in the CARRIER spelling
    /// (`{C}.ofNat n`) by [`Domain::numeral`], which range-checks it and fails
    /// closed BEFORE the kernel.
    Literal(u128),
    /// A computed operand, as a surface expression over `p0 … p{n-1}`
    /// (`"p0 & 1"`, `"p0 / 3"`), elaborated by the FROZEN [`elab_term`].
    ///
    /// **`elab_term` is where the divisor rule is enforced on this side**, and
    /// that is deliberate: it refuses `p0 / p1` and `p0 / 0` in its own words
    /// (*"division/remainder in a spec requires a positive integer literal
    /// divisor"*), from a program written years earlier for the opposite
    /// direction which knows nothing about this lane. That is the independent
    /// half of the double fault, not a restatement of the planner's rule.
    Computed(String),
}

/// Mint an E6 [`Admission`] for a **GENERAL `BEq`-CONDITIONED SELECT**
/// (§6f landing 8) — [`admit_select_beq_function`]'s tree with the two
/// coordinates that route fixes made parameters:
///
/// ```text
/// def q (a b : UInt64) : UInt64 := if (a &&& 1) == 0 then a else b   -- computed operand
/// def r (a b : UInt64) : UInt64 := if (a == b) = false then a else b -- scrutinee `false`
/// ```
///
/// A **NEW admit route**, added BESIDE [`admit_select_function`],
/// [`admit_select_literal_function`], [`admit_select_operands_function`] and
/// [`admit_select_beq_function`], all of which are untouched — the discipline
/// R2/C9 established when the literal comparison operand turned out to be
/// unrepresentable in a frozen producer's signature, and which §6f landings 3
/// and 6 each repeated rather than widening a shipped signature.
///
/// # `scrutinee` is a POLARITY, and it is the caller's to state because side B
/// READ it
///
/// The lift `<decision> = <scrutinee>` is what turns a `Bool` into a
/// proposition. `==` lifts against `Bool.true`; `(a == b) = false` lifts against
/// `Bool.false`, and the two are NOT definitionally equal — the island refuses
/// `rfl` between them, and refuses it even against the `==` body with SWAPPED
/// ARMS, which computes the same function
/// (`trust-clean-origin/tests/landing8_selection_probes.rs::l8_p2`). So a
/// caller that passed the wrong polarity would mint the COMPLEMENTARY function
/// and the gate would refuse it, which is why this is a parameter rather than
/// a flag the route infers.
///
/// `Bool.false` is minted for `false`, and a real source spells the scrutinee
/// `false` — a bare, depth-1 constant, NOT `Bool.false`. The two are
/// definitionally equal (measured, `l8_p2`), so the kernel bridges the
/// spellings; what must never happen is a READER keyed on a spelling no source
/// produces, and that constraint binds `trust-clean-origin`'s side-A recogniser,
/// not this producer.
///
/// # The instance is UNIFORM, exactly as in the narrow route
///
/// `instDecidableEqBool <decision> <scrutinee>` for every operand vocabulary
/// and both polarities, because the decision is resolved at `Bool`, one layer
/// above the carrier. That is measured, and it is the reason a COMPUTED operand
/// is cheap HERE and refused under `<`/`<=`: `if a + 1 < b` resolves its
/// decidability through a `Nat.rec`-headed normal form of the modular
/// reduction, while `if (a &&& 1) == 0` carries the computed operand VERBATIM
/// in both the proposition and the instance (`l8_p1`).
///
/// `add_decl` FULL-KERNEL-CHECKS the result; a wrong operand is a wrong term
/// the caller's definitional-reduction test refuses.
#[allow(clippy::too_many_arguments)]
pub fn admit_select_beq_operands_function(
    env: &mut Environment,
    kernel_const: &str,
    param_domains: &[Domain],
    scrutinee: bool,
    cmp_left: &SelectBeqOperand,
    cmp_right: &SelectBeqOperand,
    then_arm: SelectOperand,
    else_arm: SelectOperand,
) -> Result<Admission, String> {
    let n = param_domains.len();
    for operand in [cmp_left, cmp_right] {
        if let SelectBeqOperand::Param(index) = operand {
            if *index >= n {
                return Err(format!("select index {index} out of range for a {n}-parameter function"));
            }
        }
    }
    for operand in [then_arm, else_arm] {
        if let SelectOperand::Param(index) = operand {
            if index >= n {
                return Err(format!("select index {index} out of range for a {n}-parameter function"));
            }
        }
    }
    let d = param_domains.first().ok_or("select needs at least one parameter")?;
    if !param_domains.iter().all(|x| x == d) {
        return Err("select over mixed parameter domains is unsupported".into());
    }
    let width = match d {
        Domain::Machine(w) => *w,
        _ => return Err("select currently requires a machine-integer domain".into()),
    };
    // Under n binders the source parameter i is de Bruijn index n-1-i — the
    // convention `elab_term` uses at offset 0, so a computed operand's term
    // needs no re-indexing and there is no second place an index could be set.
    // The indices were range-checked above; the closure restates `i < n` so
    // its own body is total (the verifier checks a closure on its own, with
    // `i` unconstrained, and refuted `n - 1 - i` at `i = n` — measured
    // 2026-09-13 on `dff2b22d1`).
    let bvar = |i: usize| -> Result<Expr, String> {
        if i >= n {
            return Err(format!("select index {i} out of range for a {n}-parameter function"));
        }
        Ok(Expr::bvar(de_bruijn_index(n, i, 0)?))
    };
    let computed_ctx = if matches!(cmp_left, SelectBeqOperand::Computed(_))
        || matches!(cmp_right, SelectBeqOperand::Computed(_))
    {
        let names: Vec<String> = (0..n).map(|i| format!("p{i}")).collect();
        let uniform = uniform_var_domains(&names, d);
        Some((names, uniform))
    } else {
        None
    };
    let arm = |o: SelectOperand| -> Result<Expr, String> {
        match o {
            SelectOperand::Param(index) => bvar(index),
            SelectOperand::Literal(value) => d.numeral(value),
        }
    };
    let decision_operand = |o: &SelectBeqOperand| -> Result<Expr, String> {
        match o {
            SelectBeqOperand::Param(index) => bvar(*index),
            SelectBeqOperand::Literal(value) => d.numeral(*value),
            SelectBeqOperand::Computed(rendering) => {
                let syn: SynExpr = syn::parse_str(rendering)
                    .map_err(|e| format!("parse error in a computed select operand: {e}"))?;
                let Some((names, uniform)) = computed_ctx.as_ref() else {
                    return Err("internal: missing computed operand context".into());
                };
                elab_term(&syn, names, 0, uniform, d)
            }
        }
    };
    let ty = d.ty();
    let zero = Level::zero();
    let one = Level::succ(Level::zero());
    let inst_c = |s: &str| Expr::const_(Name::from_string(s), vec![]);
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
    let bool_lit =
        Expr::const_(Name::from_string(if scrutinee { "Bool.true" } else { "Bool.false" }), vec![]);
    // The `Bool`-level DECISION, built ONCE: it appears in the proposition AND
    // inside the instance, and two constructions of one subterm are two places
    // a spelling can drift.
    let decision = Expr::apps(
        Expr::const_(Name::from_string("BEq.beq"), vec![zero.clone()]),
        [
            ty.clone(),
            Expr::apps(
                Expr::const_(Name::from_string("instBEqOfDecidableEq"), vec![zero]),
                [ty.clone(), inst_c(width.inst_decidable_eq_const())],
            ),
            decision_operand(cmp_left)?,
            decision_operand(cmp_right)?,
        ],
    );
    let prop = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![one.clone()]),
        [bool_ty, decision.clone(), bool_lit.clone()],
    );
    let inst = Expr::apps(inst_c("instDecidableEqBool"), [decision, bool_lit]);
    // ARGUMENT ORDER: `ite α c h t e` takes THEN fourth and ELSE fifth — the
    // same polarity trap all four sibling routes document, and one that BITES
    // twice here: with `scrutinee = false` the arms read in the order the
    // SOURCE wrote them, never swapped to "compensate" for the negation.
    let body = Expr::apps(
        Expr::const_(Name::from_string("ite"), vec![one]),
        [ty.clone(), prop, inst, arm(then_arm)?, arm(else_arm)?],
    );
    let lam = (0..n).fold(body, |acc, _| Expr::lam(BinderInfo::Default, d.ty(), acc));
    let arrow_ty = (0..n).fold(d.ty(), |acc, _| Expr::arrow(d.ty(), acc));
    env.add_decl(Declaration::Definition {
        name: Name::from_string(kernel_const),
        level_params: vec![],
        type_: arrow_ty,
        value: lam,
        is_reducible: true,
    })
    .map_err(|e| format!("kernel rejected the general `==`-select defining equation: {e:?}"))?;
    // I2: reflected carrier — see `admit_constant_function`.
    Ok(Admission::reflected(kernel_const, n))
}

thread_local! {
    /// E6 brick 4: the ambient facet table for the current admission-aware
    /// elaboration. `elab_term`'s call arm reads it to elaborate an ADMITTED
    /// call to its kernel constant. Set only for the duration of
    /// [`elaborate_goal_typed_with_facets`] (via [`AdmissionScope`]) and empty
    /// otherwise, so the plain [`elaborate_goal_typed`] path — and any call
    /// with no admitted callee — still fails closed. The table is genuinely
    /// ambient context for a single synchronous elaboration; threading it
    /// through the ~40 `elab_term`/`elaborate_prop` recursion sites would add
    /// no expressiveness.
    static ADMISSION_FACETS: std::cell::RefCell<Option<FacetTable>> =
        const { std::cell::RefCell::new(None) };

    /// I3: the capability the *use site* holds for the current elaboration.
    ///
    /// The default is [`trust_symbols::Capability::Proof`], and that is a
    /// statement rather than a convenience: everything this crate builds is a
    /// kernel proposition, so every position it elaborates into is by
    /// construction a PROOF position. A CALL position must therefore *ask* for
    /// CALL — see [`elaborate_goal_typed_in`] — which is the fail-closed
    /// polarity: a future consumer that forgets to declare its position gets
    /// the weaker authority, not the stronger one, and a forgotten declaration
    /// costs a refusal instead of a wrong binary.
    static USE_SITE_CAPABILITY: std::cell::Cell<trust_symbols::Capability> =
        const { std::cell::Cell::new(trust_symbols::Capability::Proof) };
}

/// RAII guard that installs an ambient [`FacetTable`] for admission-aware
/// elaboration and RESTORES the previous value on drop — so a nested
/// elaboration cannot leak its table to an outer one, and a panic mid-
/// elaboration cannot leave a stale table behind.
struct AdmissionScope {
    previous: Option<FacetTable>,
    previous_use_site: trust_symbols::Capability,
}

impl AdmissionScope {
    /// Enter an elaboration whose use site holds `use_site`.
    ///
    /// There is deliberately no `enter(facets)` convenience that picks PROOF
    /// for you: the use site is a decision, and a default-carrying wrapper is
    /// how the decision stops being made.
    fn enter_at(facets: FacetTable, use_site: trust_symbols::Capability) -> Self {
        let previous = ADMISSION_FACETS.with(|slot| slot.replace(Some(facets)));
        let previous_use_site = USE_SITE_CAPABILITY.with(|slot| slot.replace(use_site));
        AdmissionScope { previous, previous_use_site }
    }
}

impl Drop for AdmissionScope {
    fn drop(&mut self) {
        ADMISSION_FACETS.with(|slot| *slot.borrow_mut() = self.previous.take());
        USE_SITE_CAPABILITY.with(|slot| slot.set(self.previous_use_site));
    }
}

/// Consult the ambient admission table for `callee`'s minted kernel constant.
///
/// RAW. Every position that DECIDES a binding must go through
/// [`ambient_bare_admission`] or [`ambient_call_admission`] instead, so a Rust
/// binding of the same name refuses rather than resolves (I0). The remaining
/// direct callers are domain/carrier STEERING: they choose the type a term is
/// built at and can only make an ill-typed goal the kernel then rejects, never
/// bind a name — and the deciding sites refuse the shadowed name before any
/// such goal is submitted.
fn ambient_admission(callee: &str) -> Option<Admission> {
    ADMISSION_FACETS
        .with(|slot| slot.borrow().as_ref().and_then(|table| table.admitted(callee).cloned()))
}

fn has_ambient_admission(callee: &str) -> bool {
    ADMISSION_FACETS
        .with(|slot| slot.borrow().as_ref().is_some_and(|table| table.admitted(callee).is_some()))
}

/// I0: the help line the compiler recorded for `id` when a Rust binding of the
/// specified function shadows it, else `None`.
fn ambient_shadowed_ident(id: &str) -> Option<String> {
    ADMISSION_FACETS.with(|slot| {
        slot.borrow().as_ref().and_then(|table| table.shadowed_ident(id).map(str::to_string))
    })
}

/// I0 (ref-self design §4.0): consult the ambient admission table for a BARE
/// identifier, refusing outright when a Rust binding of the specified function
/// carries that name.
///
/// SOUNDNESS. This is a pure REMOVAL of bindings: it never resolves a name the
/// raw consult would not have resolved, and the only clauses whose meaning it
/// changes are the ones that were resolving a Rust binding's name to an
/// unrelated kernel constant — i.e. the ones that were green BY CAPTURE. The
/// measured case is a by-value struct parameter, whose clause binders are its
/// scalar fields (`c.degree`), leaving the bare `c` free for a same-named
/// `clean { def c … }` to answer; a `&T` parameter has no binder at all and is
/// the same hole with a wider mouth.
///
/// The refusal fires only when an admission actually exists, so a bare name
/// with nothing to capture it keeps reporting the ordinary "unbound variable"
/// / "bindings are not exact" message it reports today.
fn ambient_bare_admission(id: &str) -> Result<Option<Admission>, String> {
    let Some(admission) = ambient_admission(id) else {
        return Ok(None);
    };
    // Trust (ref-self I1): a VIEW import is unnameable outside the spliced
    // self-call, in the BARE position as much as in a call position. It is
    // refused here STRUCTURALLY rather than incidentally: a view always has at
    // least one binder today, so the `arity >= 1` bare-name refusal below
    // already catches it, but that couples two unrelated facts by argument
    // instead of by code.
    if admission.is_self_result_only() && !is_ambient_self_fn_key(id) {
        return Err(view_import_unnameable_refusal(id, &admission));
    }
    let Some(help) = ambient_shadowed_ident(id) else {
        return Ok(Some(admission));
    };
    Err(format!(
        "a clause names VALUES: `{id}` is bound by this function's signature and has no \
         clause binder of its own, so it is NOT resolved against the admitted definition \
         `{constant}` of the same name (that reading would certify a goal about the \
         definition while the clause text says the parameter). {help}",
        constant = admission.kernel_const
    ))
}

/// I0: [`ambient_bare_admission`] for a CALL position.
///
/// `p(x)` where `p` is a binding of the specified function is a call of THAT
/// BINDING in Rust, so it must not resolve to a same-named island definition
/// or program function. `tests/ui/trust/contract_inlined_call_scope_stays_closed.rs`
/// records the same rule for the native lane and names the consequence of
/// breaking it: with a `shadow_id: fn(u64) -> u64` parameter, expanding the
/// module's `shadow_id` "would falsely turn the postcondition into `result ==
/// x`".
///
/// THERE IS NO SELF EXEMPTION, and none is needed. The one call an author never
/// wrote is the SELF-CALL [`elaborate_ensures`] splices in for `result`, and
/// Rust lets a function share its name with one of its own parameters
/// (`fn f(f: u64)`). The compiler's self identity is
/// [`self_fn_spelling`]`(def_path)` — the CANONICAL def-path (`k::f`), not the
/// bare last segment — while the shadow map holds the BARE names a signature
/// binds, so the two keyspaces do not meet on the E9 discharge lanes. A caller
/// that passes a bare self spelling AND shadows it does lose that elaboration,
/// which is the fail-closed direction and is pinned by
/// `a_bare_self_spelling_that_a_parameter_shadows_refuses_while_the_canonical_one_does_not`.
/// The alternative — exempting the self name unconditionally — would reopen the
/// bare capture for exactly `fn f(f: Cst) ensures result == f` beside
/// `clean { def f … }`.
fn ambient_call_admission(callee: &str) -> Result<Option<Admission>, String> {
    let Some(admission) = ambient_admission(callee) else {
        return Ok(None);
    };
    let Some(help) = ambient_shadowed_ident(callee) else {
        return Ok(Some(admission));
    };
    Err(format!(
        "`{callee}` is bound by this function's signature, so `{callee}(…)` is a call of that \
         binding in Rust and is NOT resolved against the admitted `{constant}` of the same \
         name (the caller chooses what that binding is, so the admitted body is not what runs). \
         {help}",
        constant = admission.kernel_const
    ))
}

/// I3: the capability the current elaboration's use site holds. PROOF unless a
/// caller entered a scope that said otherwise.
fn ambient_use_site() -> trust_symbols::Capability {
    USE_SITE_CAPABILITY.with(std::cell::Cell::get)
}

/// Like [`elaborate_goal_typed`], with a facet table consulted for program-
/// function calls in the spec. An ADMITTED call (all four facets certified AND
/// a kernel constant minted by the import step) elaborates to that constant
/// applied to its arguments; every other call still fails closed with the
/// facet-aware diagnostic. The diagnostic walk runs BEFORE elaboration so the
/// refined message wins over the backstop's generic one; it now passes over
/// admitted calls so they reach elaboration.
pub fn elaborate_goal_typed_with_facets(
    spec: &str,
    var_types: &[(&str, &str)],
    facets: &FacetTable,
) -> Result<Expr, String> {
    elaborate_goal_typed_in(trust_symbols::Capability::Proof, spec, var_types, facets)
}

/// I3: [`elaborate_goal_typed_with_facets`] with the use site's capability
/// stated.
///
/// This is the seam the decision doc's I3 control pair runs on. Pass
/// [`trust_symbols::Capability::Proof`] for a spec clause, a citation, or a
/// `clean { … }` island — every position this crate is called from today —
/// and every path in the clause resolves with no visibility ceremony, which is
/// §4.1.1's total observer capability. Pass
/// [`trust_symbols::Capability::Call`] from a position that will emit a call,
/// a load, a const evaluation, a layout or dispatch decision, or discharge an
/// unsafe obligation; a path naming a PROOF-only symbol is then refused with
/// "visible but not executable" rather than resolving to a kernel constant
/// that has no executable form.
///
/// `elaborate_goal_typed_with_facets` is exactly this function at `Proof`, so
/// the pre-I3 behaviour of every existing caller is unchanged by construction
/// rather than by inspection.
pub fn elaborate_goal_typed_in(
    use_site: trust_symbols::Capability,
    spec: &str,
    var_types: &[(&str, &str)],
    facets: &FacetTable,
) -> Result<Expr, String> {
    elaborate_goal_typed_in_mode(use_site, spec, var_types, facets, &ProofClauseInputs::strict(), None)
        .map(|clause| clause.goal)
}

/// [`elaborate_goal_typed_in`] with the CLAUSE MODE stated, and the
/// environment obligations the goal's construction created returned alongside
/// it (see [`ElaboratedClause`]).
///
/// `self_fn_name` names the contracted function when the caller has already
/// substituted `result` with a call on it; it is what the self-function
/// two-read cross-check keys on. Pass `None` from every other position — the
/// cross-check is then simply never reached, because no call is the self call.
///
/// At [`ClauseMode::Strict`] this is [`elaborate_goal_typed_in`] to the byte,
/// with an empty obligation list.
pub fn elaborate_goal_typed_in_mode(
    use_site: trust_symbols::Capability,
    spec: &str,
    var_types: &[(&str, &str)],
    facets: &FacetTable,
    inputs: &ProofClauseInputs,
    self_fn_name: Option<&str>,
) -> Result<ElaboratedClause, String> {
    elaborate_goal_typed_in_mode_with_ast(
        use_site,
        spec,
        None,
        var_types,
        facets,
        inputs,
        self_fn_name,
    )
}

fn elaborate_goal_typed_in_mode_with_ast(
    use_site: trust_symbols::Capability,
    spec: &str,
    parsed_ast: Option<&SynExpr>,
    var_types: &[(&str, &str)],
    facets: &FacetTable,
    inputs: &ProofClauseInputs,
    self_fn_name: Option<&str>,
) -> Result<ElaboratedClause, String> {
    // Drain any residue from an earlier elaboration before this one records
    // its own: the accumulator is thread-local and a caller that dropped a
    // result on an `Err` path must not leak an obligation into the next goal.
    let _ = take_required_signed_lifts();
    let _lift = ProofLiftScope::enter(inputs, self_fn_name);
    // Trust (ref-self I1): the self-call key, in EVERY mode. See `SELF_FN_KEY`.
    let _self_fn = SelfFnScope::enter(self_fn_name);
    let goal = elaborate_goal_typed_in_inner(use_site, spec, parsed_ast, var_types, facets)?;
    Ok(ElaboratedClause { goal, required_signed_lift_widths: take_required_signed_lifts() })
}

fn elaborate_goal_typed_in_inner(
    use_site: trust_symbols::Capability,
    spec: &str,
    parsed_ast: Option<&SynExpr>,
    var_types: &[(&str, &str)],
    facets: &FacetTable,
) -> Result<Expr, String> {
    // E3: a quantified clause is not syn-parseable as a whole, so the facet
    // diagnostic walk runs over the pre-parsed leaves instead; the admission
    // scope then covers the same quantified elaboration path.
    if parsed_ast.is_none() && clause_uses_quantifier_fragment(spec) {
        let clause = parse_qclause(spec, true)?;
        if let Some(err) = qclause_first_call_facet_error(&clause, facets) {
            return Err(err);
        }
        let _scope = AdmissionScope::enter_at(facets.clone(), use_site);
        return elaborate_parsed_qclause_typed(&clause, var_types);
    }
    if let Some(ast) = parsed_ast {
        if let Some(err) = first_call_facet_error(ast, facets) {
            return Err(err);
        }
        let _scope = AdmissionScope::enter_at(facets.clone(), use_site);
        return elaborate_parsed_goal_typed(ast, var_types);
    }
    let ast: SynExpr = syn::parse_str(spec).map_err(|e| format!("parse error: {e}"))?;
    if let Some(err) = first_call_facet_error(&ast, facets) {
        return Err(err);
    }
    let _scope = AdmissionScope::enter_at(facets.clone(), use_site);
    elaborate_parsed_goal_typed(&ast, var_types)
}

/// The fixed head of the refusal [`elaborate_ensures`] returns when the clause
/// binds `result` and the specified function has no E6 kernel import. Named
/// so a diagnostic consumer can recognise THIS refusal without re-deriving the
/// condition (see [`is_self_not_e6_admitted_refusal`]); the message text itself
/// is unchanged.
const SELF_NOT_E6_ADMITTED_REFUSAL_HEAD: &str = "ensures discharge requires the specified function";

/// Whether `reason` is [`elaborate_ensures`]'s "the specified function is not
/// E6-admitted" refusal. Diagnostics only: the compiler uses it to decide
/// whether to explain WHICH facet or body shape kept the function out of the
/// E6 import. It confers nothing and no verdict reads it.
#[must_use]
pub fn is_self_not_e6_admitted_refusal(reason: &str) -> bool {
    reason.starts_with(SELF_NOT_E6_ADMITTED_REFUSAL_HEAD)
}

/// Elaborate an `ensures` clause into the kernel proposition a cited theorem must
/// prove to DISCHARGE the postcondition VC (E9 discharge criterion — see
/// `docs/design-notes/2026-07-15-e9-discharge-criterion.md`).
///
/// The compiler's postcondition VC binds `result` to the function's actual
/// return value, whereas the ordinary clause elaborator treats `result` as a free
/// variable and ∀-closes over it — yielding a generally-FALSE statement (`∀ result
/// x, result ≤ x`) that no honest theorem proves. This constructor removes that
/// mismatch: for a function `self_fn` that is itself E6-admitted (its faithful,
/// kernel-rechecked defining equation `self_fn_def` is in the environment), the
/// return value IS `self_fn_def(params)`, so it rewrites every `result` occurrence
/// to a call `self_fn(params…)` and elaborates over the PARAMETERS only. The result
/// is `∀ params, Q(params, self_fn_def(params))` — the postcondition for all
/// inputs; the concrete VC is one instance, so a theorem of this type proves it
/// (a sound weakening once domains match).
///
/// `param_types` are the parameters ONLY (no `result`). Fails closed (no
/// admission of `self_fn`, unsupported domain, non-exact bindings) exactly like
/// the other typed elaborators. This constructs the goal only; it grants NO VC
/// authority — the grading wire + its faithfulness shadow-check are the separate,
/// soundness-critical piece (design note §4.2, §5).
pub fn elaborate_ensures(
    clause: &str,
    param_types: &[(&str, &str)],
    self_fn_name: &str,
    facets: &FacetTable,
) -> Result<Expr, String> {
    elaborate_ensures_in(clause, param_types, self_fn_name, facets, &ProofClauseInputs::strict())
        .map(|clause| clause.goal)
}

/// [`elaborate_ensures`] with the CLAUSE MODE stated.
///
/// This is the ONLY way into the nat-lift fragment for an `ensures` clause, and
/// [`elaborate_ensures`] is exactly this function at [`ClauseMode::Strict`], so
/// the pre-existing behaviour of every caller is unchanged BY CONSTRUCTION
/// rather than by inspection — the same discipline
/// `elaborate_goal_typed_with_facets` already uses for the I3 capability.
///
/// A body mint never reaches here: `admit_expr_function` and its siblings call
/// `elab_term` directly, so a Rust BODY cannot acquire a lift even if a caller
/// handed the mint loop a `ProofLift` facet table.
pub fn elaborate_ensures_in(
    clause: &str,
    param_types: &[(&str, &str)],
    self_fn_name: &str,
    facets: &FacetTable,
    inputs: &ProofClauseInputs,
) -> Result<ElaboratedClause, String> {
    let source = ensures_goal_source(clause, param_types, self_fn_name, facets)?;
    let used = discharge_used_bindings(&source, param_types);
    elaborate_goal_typed_in_mode_with_ast(
        trust_symbols::Capability::Proof,
        &source.src,
        source.parsed_ast.as_ref(),
        &used,
        facets,
        inputs,
        Some(self_fn_name),
    )
}

/// The clause source [`elaborate_ensures`] actually elaborates, plus whether it
/// took the E3 quantifier route.
///
/// Factored out so the unconditional goal `G0` ([`elaborate_ensures`]) and the
/// under-`requires` goal `G1` ([`elaborate_ensures_under_requires`]) share ONE
/// rewrite prefix — field rewrite, self-admission gate, minted-parameter
/// agreement, self-identity round trip, `result → self_fn(p0..pn)`. Two copies
/// of that prefix could drift apart, and a drifted `G1` would be a DIFFERENT
/// statement wearing the same clause's name (design revision 2 §2.2 step 1).
struct EnsuresGoalSource {
    /// The rewritten clause the elaborator sees when `parsed_ast` is `None`.
    src: String,
    /// Pre-parsed and rewritten AST when the clause stays in the syn-parsed
    /// non-quantifier fragment, avoiding intermediate `quote!(...).to_string()`
    /// formatting and double `syn::parse_str` re-parses.
    parsed_ast: Option<SynExpr>,
    /// `true` when the clause is in the E3 quantifier/implication fragment. `G1`
    /// is not built for such a clause: its binder structure is authored inside
    /// the clause, so prepending hypothesis arrows would produce a goal whose
    /// binder order no honest theorem statement predicts.
    quantified: bool,
}

fn ensures_goal_source<T>(
    clause: &str,
    param_types: &[(&str, T)],
    self_fn_name: &str,
    facets: &FacetTable,
) -> Result<EnsuresGoalSource, String> {
    if self_fn_name.is_empty() {
        return Err("elaborate_ensures requires the specified function's name".to_string());
    }
    // A quantified/implication clause (E3 fragment) is not Rust-parseable by syn
    // and cannot carry the `result` substitution yet; route it straight to the
    // quantified elaborator over just the parameters it uses. `result` inside a
    // quantifier is a free variable there and stays fail-closed (a deeper slice).
    if clause_uses_quantifier_fragment(clause) {
        return Ok(EnsuresGoalSource {
            src: clause.to_string(),
            parsed_ast: None,
            quantified: true,
        });
    }
    let param_names: Vec<String> = param_types.iter().map(|(n, _)| (*n).to_string()).collect();
    let ast: SynExpr = syn::parse_str(clause).map_err(|e| format!("parse error: {e}"))?;
    // FIELD PROJECTIONS FIRST. A struct-returning body has no whole-function
    // import -- only one constant per field -- so the admission lookup below
    // would fail closed on a clause that never needed it. Rewriting
    // `result.<field>` here leaves the clause free of `result` whenever every
    // mention was a projection, and the ordinary path then elaborates it.
    let had_result_field = mentions_result_field(&ast);
    let ast = if had_result_field {
        rewrite_result_fields(&ast, self_fn_name, &param_names, facets)?
    } else {
        ast
    };
    let can_reuse_ast = !had_result_field
        && !self_fn_name.starts_with("forall")
        && !self_fn_name.starts_with("exists");
    // A clause that never mentions `result` is a ∀-params statement independent
    // of the function's return value — its proof covers the postcondition for
    // ANY body, so the SELF-admission gate is required only when `result` must
    // be substituted with the defining equation. (Calls inside the clause are
    // still individually gated on THEIR admissions by the elaborator.)
    if !mentions_result(&ast) {
        if can_reuse_ast {
            return Ok(EnsuresGoalSource {
                src: String::new(),
                parsed_ast: Some(ast),
                quantified: false,
            });
        }
        let rewritten_src = quote::quote!(#ast).to_string();
        return Ok(EnsuresGoalSource {
            src: rewritten_src,
            parsed_ast: None,
            quantified: false,
        });
    }
    let Some(admission) = facets.admitted(self_fn_name) else {
        // `result` has no kernel denotation unless the function is E6-admitted;
        // fail closed (design note §3 restriction), same as any un-admitted call.
        return Err(format!(
            "{SELF_NOT_E6_ADMITTED_REFUSAL_HEAD} `{self_fn_name}` to be \
             E6-admitted (its defining equation kernel-imported); it is not"
        ));
    };
    // DERIVED-PARAMETER AGREEMENT (E6/E9 widening increment 7). When the mint
    // recorded the clause-side names of the binders it actually bound, the
    // self-call built below must apply the constant to exactly those names, in
    // exactly that order. The two lists are computed independently — this one
    // from the compiler's HIR-side signature table, the recorded one from the
    // extracted IR — and an ORDER disagreement between them is the one failure
    // the kernel cannot catch: the goal still types, and a theorem about
    // `coeff` would discharge a clause about `degree`. Refuse instead.
    if let Some(minted) = admission.param_names.as_ref().filter(|minted| **minted != param_names) {
        return Err(format!(
            "the clause's parameter list {param_names:?} disagrees with the parameter list the \
             E6 import of `{self_fn_name}` was minted over ({minted:?}); the two flattenings of \
             the same signature must agree exactly, so the discharge fails closed"
        ));
    }
    // Build the substitute `self_fn(p0, p1, …)` once, then splice it in for every
    // `result`. Parsing a synthesized call string reuses syn's own node shapes.
    let call_src = format!("{self_fn_name}({})", param_names.join(", "));
    let self_call: SynExpr = syn::parse_str(&call_src)
        .map_err(|e| format!("internal: could not build self-call `{call_src}`: {e}"))?;
    // SELF-IDENTITY ROUND TRIP (soundness). `admission` above was looked up
    // under `self_fn_name`, but the substitute spliced in for `result` is a
    // parsed CALL, and the elaborator re-derives its admission key from the
    // parsed syntax with `callee_path` — which reconstructs the path from
    // `syn`'s segments and DROPS a qualified-impl qself (`<i64 as T>::f`
    // re-keys as `T::f`). If the two keys can differ, `result` could be bound
    // to a DIFFERENT item's defining equation than the one whose admission was
    // checked here. Require the spelling to reproduce itself exactly; anything
    // else fails closed. `self_fn_spelling` already excludes the known
    // offenders, so this is the independent backstop — it also holds for any
    // future caller that passes a hand-built identity.
    let SynExpr::Call(self_call_expr) = &self_call else {
        return Err(format!("internal: self-call `{call_src}` did not parse as a call expression"));
    };
    let round_tripped = callee_path(self_call_expr);
    if round_tripped != self_fn_name {
        return Err(format!(
            "the specified function `{self_fn_name}` is not spellable as a spec call: it \
             re-resolves as `{round_tripped}`, which may name a different item, so binding \
             `result` to its defining equation fails closed"
        ));
    }
    let rewritten = rewrite_result_to(&ast, &self_call)?;
    if can_reuse_ast {
        return Ok(EnsuresGoalSource {
            src: String::new(),
            parsed_ast: Some(rewritten),
            quantified: false,
        });
    }
    let rewritten_src = quote::quote!(#rewritten).to_string();
    // Elaborate over the parameters only — `result` is gone, replaced by the
    // admitted self-call, which `elab_term` resolves to `self_fn_def(params)`.
    // Filter to the params the rewritten clause actually uses so a clause that
    // constrains only a SUBSET of the parameters (e.g. a quantified clause, or
    // `ensures result >= 0`) still binds exactly its free variables.
    Ok(EnsuresGoalSource { src: rewritten_src, parsed_ast: None, quantified: false })
}

/// For the ensures-discharge path, the subset of `param_types` whose names are
/// FREE variables of `clause` — a discharge goal over only the variables the
/// clause uses is sound (an unused parameter is simply not constrained), and it
/// keeps the exact-binding gate satisfiable for a clause that references fewer
/// than all the parameters (quantified clauses, constant bounds, single-param
/// predicates in a multi-param function). Routes quantified vs plain clauses the
/// same way `elaborate_goal_typed` does; on any parse failure it returns the
/// full list unchanged so the elaborator reports the real error.
fn discharge_used_bindings<'a, T: Clone>(
    source: &EnsuresGoalSource,
    param_types: &[(&'a str, T)],
) -> Vec<(&'a str, T)> {
    let free: Vec<String> = if let Some(ast) = &source.parsed_ast {
        let mut acc = Vec::new();
        collect_vars(ast, &mut acc);
        acc
    } else if clause_uses_quantifier_fragment(&source.src) {
        match parse_qclause(&source.src, true) {
            Ok(qc) => {
                let mut acc = Vec::new();
                collect_qclause_free_vars(&qc, &mut Vec::new(), &mut acc);
                acc
            }
            Err(_) => return param_types.to_vec(),
        }
    } else {
        match syn::parse_str::<SynExpr>(&source.src) {
            Ok(ast) => {
                let mut acc = Vec::new();
                collect_vars(&ast, &mut acc);
                acc
            }
            Err(_) => return param_types.to_vec(),
        }
    };
    param_types.iter().filter(|(n, _)| free.iter().any(|v| v == *n)).cloned().collect()
}

// ---------------------------------------------------------------------------
// A1 — `requires` as kernel hypotheses (design revision 2 `requires-hyps` §2).
//
// `elaborate_ensures` builds the UNCONDITIONAL goal
//
//     G0 := ∀ (value binders), Q(params, f_def params)
//
// so a theorem that is true only under the function's own precondition cannot
// be cited at all. This section adds the strictly weaker second rung
//
//     G1 := ∀ (value binders), H_0 → … → H_{n-1} → Q(params, f_def params)
//
// where each `H_j` is the elaboration of one ELIGIBLE `requires` clause.
//
// SOUNDNESS, stated once. A conclusion and a hypothesis have OPPOSITE polarity.
// For the conclusion the discharge criterion needs `P_Q ⇒ F_Q` (the kernel
// proposition implies the formula callers are charged). For a hypothesis it
// needs `F_R ⇒ P_R`: whatever callers are actually CHARGED must imply what the
// theorem is allowed to CONSUME. Three rules keep that direction honest:
//
//   1. a hypothesis is derived from the QUERY-OWNED canonical proposition the
//      caller is charged — never from source-span text (the caller passes it in
//      [`HypothesisInput::canonical_text`] and cross-checks it, see
//      `spec_clean_uncited_denotation` on the compiler side);
//   2. only the arithmetic-free syntactic allow-list `E-allow`
//      ([`hypothesis_allow_listed`]) is eligible, because it is the fragment on
//      which the Clean reading and the charged reading provably agree. Machine
//      arithmetic is the counterexample that forces this: in Clean `+` on
//      `UInt64` WRAPS while callers are charged the non-wrapping reading, so
//      `requires a + b > 10` would hand the theorem a hypothesis that
//      `a = u64::MAX, b = 1` satisfies in the charged reading and refutes in the
//      Clean one;
//   3. anything else is OMITTED, never approximated. Omission is always the
//      sound direction — `(∀p, Q) ⇒ (∀p, H → Q)` — and it is disclosed.
//
// Omitting every clause leaves `G1 = G0` with no arrow, which is why a build
// with zero bound hypotheses is refused rather than returned: the caller must
// not be able to spend a second kernel grade on the goal it already has.
// ---------------------------------------------------------------------------

/// One `requires` clause offered to [`elaborate_ensures_under_requires`] as a
/// candidate hypothesis.
///
/// `canonical_text` is the QUERY-OWNED canonical spelling — the text that
/// re-parses to the identical `Formula`/domain tree callers are charged — and it
/// is the only spelling this crate elaborates. `authored_text` is carried for
/// diagnostics and is never elaborated. `query_bindings` is the query's own
/// view of each free variable's carrier; every free variable of
/// `canonical_text` must have a row here and it must agree with the caller's
/// parameter table, or the clause is omitted. An EMPTY `query_bindings` is not
/// "no opinion": a clause with free variables and no query view is omitted.
#[derive(Debug, Clone)]
pub struct HypothesisInput {
    /// Dense index of this contract in the function's contract list.
    pub contract_index: usize,
    /// Canonical, query-owned clause text. Elaborated.
    pub canonical_text: String,
    /// Authored spelling. Diagnostics only — NEVER elaborated.
    pub authored_text: String,
    /// The query's own `name → Rust carrier` view of this clause's variables.
    pub query_bindings: Vec<(String, String)>,
}

/// What became of one candidate hypothesis.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum HypothesisDisposition {
    /// Carried as arrow `binder_index` of `G1` (0 = outermost hypothesis).
    Bound { binder_index: usize },
    /// Not carried. The goal is correspondingly HARDER, never weaker.
    Omitted { reason: String },
}

/// One row per `requires` contract, in contract order — what v6/D1 requires be
/// reported: exactly what was graded.
#[derive(Debug, Clone)]
pub struct HypothesisRow {
    pub contract_index: usize,
    pub canonical_text: String,
    pub authored_text: String,
    pub disposition: HypothesisDisposition,
    /// Trust (OR-A1): the LIFTED spelling `T_j` of `canonical_text` that the
    /// kernel-canonical goal `G1★` carries for this row
    /// ([`lift_hypothesis_source`]) — `Some` exactly when the row is `Bound`
    /// AND `G1★` was built. Disclosure only; the elaborated `Expr` is what is
    /// graded.
    pub lifted_text: Option<String>,
}

/// The `G1` goal plus the disclosure that must travel with it.
#[derive(Debug, Clone)]
pub struct EnsuresUnderRequires {
    /// `∀ (value binders), H_0 → … → H_{n-1} → Q`.
    pub goal: Expr,
    /// Clause-side names of the value binders, outermost first.
    pub value_binders: Vec<String>,
    /// One row per candidate, in contract order.
    pub hypotheses: Vec<HypothesisRow>,
    /// Trust (OR-A1, Inc 1a): `G1★` — the SAME binder list, the SAME conclusion
    /// and the SAME bound hypothesis set as [`Self::goal`], with each hypothesis
    /// carried in its LIFTED mathematical reading `T_j` instead of its Clean
    /// (allow-listed) reading `H_j`.
    ///
    /// `T_j` is built from the query-owned `canonical_text` — the text whose
    /// `:984` round trip re-parses to exactly the `Formula` callers are charged —
    /// by rewriting every integer parameter atom `x` to `(x as nat)` (unsigned)
    /// or `(x as int)` (signed) and elaborating the result through the EXISTING
    /// nat-lift path ([`lift_for`]'s closed table), over the same binders at
    /// offset 0. No new `Formula → Expr` translator exists: the lift table is
    /// already in the `EnsuresCitationDischarge` goal-construction base
    /// (`docs/TCB.md`). On the arithmetic-free fragment `E-allow` every lift
    /// row is an exact, order-preserving injection, so `T_j` holds exactly when
    /// the charged proposition does.
    ///
    /// This is NOT the implicit lift OR-1 bars: OR-1 is about a
    /// USER-authored clause acquiring a cast the author did not write. Here the
    /// compiler states, in the kernel, the reading of a proposition the caller
    /// is already charged, and only on a fragment with no arithmetic, where
    /// wrapping and unbounded readings cannot disagree.
    ///
    /// `None` when some bound hypothesis has no lifted reading (a pointer-sized
    /// carrier the lift table refuses, a carrier outside the table); the reason
    /// is in [`Self::canonical_refusal`]. Grading `G1★` grants nothing by
    /// itself: the ladder in `trust_certify::clean_island` grades it, and the
    /// compiler decides what a certified grade on it is worth.
    pub canonical_goal: Option<Expr>,
    /// Why [`Self::canonical_goal`] is `None`, when it is.
    pub canonical_refusal: Option<String>,
    /// Signed widths whose seeded lift model the conclusion OR a lifted
    /// hypothesis names (the union — H6). The holder of the kernel environment
    /// must seed each before typing or grading EITHER goal; see
    /// [`ElaboratedClause::required_signed_lift_widths`].
    pub required_signed_lift_widths: Vec<MachineSIntWidth>,
}

impl EnsuresUnderRequires {
    /// How many hypotheses the goal actually carries.
    #[must_use]
    pub fn bound_count(&self) -> usize {
        self.hypotheses
            .iter()
            .filter(|r| matches!(r.disposition, HypothesisDisposition::Bound { .. }))
            .count()
    }

    /// The canonical texts of the bound hypotheses, outermost first.
    #[must_use]
    pub fn bound_texts(&self) -> Vec<&str> {
        let mut bound: Vec<(usize, &str)> = self
            .hypotheses
            .iter()
            .filter_map(|r| match &r.disposition {
                HypothesisDisposition::Bound { binder_index } => {
                    Some((*binder_index, r.canonical_text.as_str()))
                }
                HypothesisDisposition::Omitted { .. } => None,
            })
            .collect();
        bound.sort_by_key(|(i, _)| *i);
        bound.into_iter().map(|(_, t)| t).collect()
    }
}

/// Why one build attempt could not carry a particular hypothesis.
struct OmitOne {
    contract_index: usize,
    reason: String,
}

/// Build `G1` — [`elaborate_ensures`]'s goal with the ELIGIBLE `requires`
/// clauses prepended as kernel hypotheses (design revision 2 §2.2).
///
/// The conclusion is built by the SAME rewrite prefix `elaborate_ensures` uses
/// ([`ensures_goal_source`]), so `G0` and `G1` cannot state different
/// postconditions. Binder order is load-bearing and fixed: every value binder
/// first, in `G0`'s order, then every variable free in some eligible hypothesis
/// and not already present, in SIGNATURE order; then the hypothesis arrows in
/// contract order. A theorem must be stated with exactly those binders.
///
/// De Bruijn discipline. Every sub-proposition — conclusion and hypotheses
/// alike — is elaborated at offset 0 over the same binder list, which is the
/// path every clause in this crate takes. The shift into the arrow telescope is
/// then performed by the KERNEL's own `Expr::lift`: `h_j` sits under `j`
/// hypothesis binders, the conclusion under all `n`. There is deliberately no
/// hand-computed offset: an off-by-one between two same-carrier binders is
/// WELL-TYPED (it would silently turn `c <= b` into `b <= a`), so the type
/// checker cannot be the guard — a single code path plus the semantic control
/// `g1_hypothesis_binds_the_authored_parameters` is.
///
/// Fails closed: a quantifier-fragment clause, a conclusion outside the
/// fragment, or ZERO eligible hypotheses all return `Err`. Returning `G0` under
/// this name would let a caller spend a second kernel grade on a goal it has
/// already graded, and report it as a conditional discharge.
///
/// This is [`elaborate_ensures_under_requires_in`] at [`ClauseMode::Strict`], so
/// every pre-existing caller builds the same `G1` it always did.
pub fn elaborate_ensures_under_requires(
    clause: &str,
    param_types: &[(&str, &str)],
    self_fn_name: &str,
    facets: &FacetTable,
    hyps: &[HypothesisInput],
) -> Result<EnsuresUnderRequires, String> {
    elaborate_ensures_under_requires_in(
        clause,
        param_types,
        self_fn_name,
        facets,
        hyps,
        &ProofClauseInputs::strict(),
    )
}

/// Trust (OR-A1, Inc 0): [`elaborate_ensures_under_requires`] with the CLAUSE
/// MODE of the CONCLUSION stated — the `ProofClauseInputs` threading the
/// unconditional rung already has ([`elaborate_ensures_in`]).
///
/// Without it a lifted conclusion (`ensures (result as nat) == spec(k as nat)`)
/// is `unsupported term shape` here while the unconditional rung accepts it, so
/// the second rung was unreachable for exactly the clauses the nat-lift work
/// made statable (measured: probe `r1`, "outside the exact statement fragment").
///
/// The mode governs the CONCLUSION only. The allow-listed hypotheses `H_j` are
/// in `E-allow`, which admits no cast and no call, so no mode-dependent branch
/// of the elaborator is reachable from them; the lifted hypotheses `T_j` of
/// `G1★` are always elaborated in `ProofLift` mode, because a cast is what they
/// are made of (see [`EnsuresUnderRequires::canonical_goal`]).
///
/// The signed lift widths BOTH goals name are returned as one union
/// ([`EnsuresUnderRequires::required_signed_lift_widths`]); the caller seeds
/// them before grading either.
pub fn elaborate_ensures_under_requires_in(
    clause: &str,
    param_types: &[(&str, &str)],
    self_fn_name: &str,
    facets: &FacetTable,
    hyps: &[HypothesisInput],
    inputs: &ProofClauseInputs,
) -> Result<EnsuresUnderRequires, String> {
    // Drain any residue from an earlier elaboration (same discipline as
    // `elaborate_goal_typed_in_mode`): a caller that dropped a result on an
    // `Err` path must not leak an obligation into this goal.
    let _ = take_required_signed_lifts();
    // The conclusion's mode, with the self-call key the lift's self-function
    // two-read cross-check needs. `SELF_FN_KEY` is deliberately NOT installed:
    // a `self_result_only` (parameter-view) admission stays unnameable on this
    // rung, which keeps a view function out of the conditional lane entirely —
    // the scope limit the compiler states in its note.
    let _lift = ProofLiftScope::enter(inputs, Some(self_fn_name));
    let source = ensures_goal_source(clause, param_types, self_fn_name, facets)?;
    if source.quantified {
        return Err(
            "an `ensures` clause in the quantifier/implication fragment authors its own binder \
             structure, so the compiler does not build the under-`requires` goal for it; state \
             the precondition inside the clause with `==>` instead"
                .to_string(),
        );
    }
    let ast_q: SynExpr = match source.parsed_ast {
        Some(ast) => ast,
        None => syn::parse_str(&source.src).map_err(|e| format!("parse error: {e}"))?,
    };
    // Same order as `elaborate_goal_typed_in`: the facet diagnostic walk runs
    // BEFORE elaboration so its refined message wins over the backstop's.
    if let Some(err) = first_call_facet_error(&ast_q, facets) {
        return Err(err);
    }
    let _scope = AdmissionScope::enter_at(facets.clone(), trust_symbols::Capability::Proof);

    let mut omitted: BTreeMap<usize, String> = BTreeMap::new();
    // At most one restart per candidate: each restart omits one more clause, and
    // an empty eligible set is refused, so this terminates.
    for _ in 0..=hyps.len() {
        // Each attempt records its own seeding obligations: an abandoned
        // attempt must not leave a width behind for the one that succeeds.
        let _ = take_required_signed_lifts();
        match build_under_requires(&ast_q, param_types, hyps, &omitted) {
            Ok(built) => return Ok(built),
            Err(Ok(one)) => {
                omitted.insert(one.contract_index, one.reason);
            }
            Err(Err(fatal)) => return Err(fatal),
        }
    }
    Err("no `requires` clause of this function is eligible as a kernel hypothesis".to_string())
}

/// One attempt at `G1` with `omitted` already excluded.
///
/// `Err(Ok(one))` means "restart without this clause"; `Err(Err(msg))` is fatal
/// for the whole goal.
#[allow(clippy::result_large_err)]
fn build_under_requires(
    ast_q: &SynExpr,
    param_types: &[(&str, &str)],
    hyps: &[HypothesisInput],
    omitted: &BTreeMap<usize, String>,
) -> Result<EnsuresUnderRequires, Result<OmitOne, String>> {
    // (1) Eligibility, in contract order. Parse + allow-list + query-binding
    // agreement happen before any binder is chosen, so an ineligible clause
    // never contributes a binder.
    let mut eligible: Vec<(&HypothesisInput, SynExpr, Vec<String>)> = Vec::new();
    for hyp in hyps {
        if omitted.contains_key(&hyp.contract_index) {
            continue;
        }
        let ast: SynExpr = match syn::parse_str(&hyp.canonical_text) {
            Ok(ast) => ast,
            Err(e) => {
                return Err(Ok(OmitOne {
                    contract_index: hyp.contract_index,
                    reason: format!("its canonical text does not parse as a clause ({e})"),
                }));
            }
        };
        if let Err(reason) = hypothesis_allow_listed(&ast, param_types) {
            return Err(Ok(OmitOne { contract_index: hyp.contract_index, reason }));
        }
        let mut vars = Vec::new();
        collect_vars(&ast, &mut vars);
        // The query's own carrier view must agree with the parameter table this
        // goal's binders are typed from. Two independent flattenings of one
        // signature that DISAGREE is the failure the kernel cannot catch: the
        // goal still types and the theorem proves the wrong statement.
        for v in &vars {
            let Some(declared) = param_types.iter().find(|(n, _)| n == v).map(|(_, t)| *t) else {
                return Err(Ok(OmitOne {
                    contract_index: hyp.contract_index,
                    reason: format!(
                        "it names `{v}`, which is not a parameter row of this function"
                    ),
                }));
            };
            let Some(owned) = hyp.query_bindings.iter().find(|(n, _)| n == v).map(|(_, t)| t)
            else {
                return Err(Ok(OmitOne {
                    contract_index: hyp.contract_index,
                    reason: format!(
                        "the contract query publishes no carrier for `{v}`, so the charged \
                         reading of the clause cannot be confirmed"
                    ),
                }));
            };
            if owned != declared {
                return Err(Ok(OmitOne {
                    contract_index: hyp.contract_index,
                    reason: format!(
                        "the contract query reads `{v}` at `{owned}` while the signature row \
                         says `{declared}`; the two flattenings must agree exactly"
                    ),
                }));
            }
        }
        eligible.push((hyp, ast, vars));
    }
    if eligible.is_empty() {
        return Err(Err(
            "no `requires` clause of this function is eligible as a kernel hypothesis".to_string(),
        ));
    }

    // (2) Binder list: G0's list byte for byte, then the hypotheses' extra
    // variables in SIGNATURE order (never in clause order — the binder list must
    // be a function of the signature, not of the order clauses were authored).
    let mut vars: Vec<String> = Vec::new();
    collect_vars(ast_q, &mut vars);
    vars.retain(|v| {
        param_types.iter().any(|(n, _)| n == v) || !has_ambient_admission(v)
    });
    let mut extra: BTreeSet<&str> = BTreeSet::new();
    for (_, _, hyp_vars) in &eligible {
        for v in hyp_vars {
            if !vars.iter().any(|existing| existing == v) {
                extra.insert(v.as_str());
            }
        }
    }
    for (name, _) in param_types {
        if extra.contains(name) {
            vars.push((*name).to_string());
        }
    }
    let used: Vec<(&str, &str)> =
        param_types.iter().filter(|(n, _)| vars.iter().any(|v| v == n)).copied().collect();
    let var_domains = exact_typed_bindings(&vars, &used).map_err(Err)?;

    // (3) ONE offset code path: everything at offset 0 over `vars`.
    let q_body = elaborate_prop_multi(ast_q, &vars, 0, &var_domains).map_err(Err)?;
    let mut hyp_bodies: Vec<Expr> = Vec::with_capacity(eligible.len());
    for (hyp, ast, _) in &eligible {
        match elaborate_prop_multi(ast, &vars, 0, &var_domains) {
            Ok(body) => hyp_bodies.push(body),
            Err(reason) => {
                return Err(Ok(OmitOne {
                    contract_index: hyp.contract_index,
                    reason: format!("it is outside the kernel fragment ({reason})"),
                }));
            }
        }
    }

    // (4) The arrow telescope, shifted by the KERNEL's own lift.
    let n = u32::try_from(hyp_bodies.len())
        .map_err(|_| Err("too many `requires` clauses to carry as hypotheses".to_string()))?;
    let mut body = q_body.lift(n);
    for (j, h) in hyp_bodies.iter().enumerate().rev() {
        let shift = u32::try_from(j).unwrap_or(u32::MAX);
        body = Expr::pi(BinderInfo::Default, h.lift(shift), body);
    }
    let goal = close_over_multi(&vars, body, &var_domains).map_err(Err)?;
    // The seeding obligations of the conclusion (the allow-listed hypotheses
    // are cast-free and name none). Taken BEFORE `G1★` is built so its own
    // obligations can be added only when it is.
    let mut required_signed_lift_widths = take_required_signed_lifts();

    // (4★) Trust (OR-A1, Inc 1a): `G1★` over the SAME binders, the SAME
    // conclusion body and the SAME eligible set, each hypothesis in its lifted
    // reading. A miss is disclosed, never fatal: `G1` stands on its own.
    let (canonical_goal, canonical_refusal, lifted_texts) =
        match build_canonical_under_requires(&q_body, &eligible, param_types, &vars, &var_domains)
        {
            Ok((canonical, texts, widths)) => {
                for width in widths {
                    if !required_signed_lift_widths.contains(&width) {
                        required_signed_lift_widths.push(width);
                    }
                }
                (Some(canonical), None, texts)
            }
            Err(reason) => (None, Some(reason), Vec::new()),
        };

    // (5) Rows, in CONTRACT order — the disclosure v6/D1 asks for.
    let mut binder_of: BTreeMap<usize, usize> = BTreeMap::new();
    for (j, (hyp, _, _)) in eligible.iter().enumerate() {
        binder_of.insert(hyp.contract_index, j);
    }
    let hypotheses = hyps
        .iter()
        .map(|hyp| HypothesisRow {
            contract_index: hyp.contract_index,
            canonical_text: hyp.canonical_text.clone(),
            authored_text: hyp.authored_text.clone(),
            disposition: match binder_of.get(&hyp.contract_index) {
                Some(binder_index) => HypothesisDisposition::Bound { binder_index: *binder_index },
                None => HypothesisDisposition::Omitted {
                    reason: omitted
                        .get(&hyp.contract_index)
                        .cloned()
                        .unwrap_or_else(|| "it was not offered as a hypothesis".to_string()),
                },
            },
            lifted_text: binder_of
                .get(&hyp.contract_index)
                .and_then(|binder_index| lifted_texts.get(*binder_index))
                .cloned(),
        })
        .collect();
    Ok(EnsuresUnderRequires {
        goal,
        value_binders: vars,
        hypotheses,
        canonical_goal,
        canonical_refusal,
        required_signed_lift_widths,
    })
}

/// Trust (OR-A1, Inc 1a): build `G1★` — see
/// [`EnsuresUnderRequires::canonical_goal`] for what it is and why.
///
/// ONE offset code path, the same one `G1` takes: each `T_j` is elaborated at
/// offset 0 over `vars`/`var_domains` (the very binder list `G1` was closed
/// over), and the telescope is shifted by the KERNEL's own `Expr::lift`, so the
/// two goals can differ ONLY in the hypothesis bodies. `q_body` is `G1`'s own
/// conclusion body, reused rather than re-elaborated, so the conclusions are
/// identical by construction.
///
/// Returns the goal, the lifted spelling of each eligible hypothesis in binder
/// order, and the signed widths the lifted hypotheses name.
#[allow(clippy::type_complexity)]
fn build_canonical_under_requires(
    q_body: &Expr,
    eligible: &[(&HypothesisInput, SynExpr, Vec<String>)],
    param_types: &[(&str, &str)],
    vars: &[String],
    var_domains: &BTreeMap<String, Domain>,
) -> Result<(Expr, Vec<String>, Vec<MachineSIntWidth>), String> {
    // The lift is what `T_j` is made of, so it is elaborated in `ProofLift`
    // mode whatever mode the conclusion was built in. No self function: a
    // `requires` clause names no call (E-allow), so the self-call cross-check
    // is unreachable from here.
    let built = {
        let _lift = ProofLiftScope::enter(&ProofClauseInputs::proof_lift(None), None);
        build_canonical_under_requires_inner(q_body, eligible, param_types, vars, var_domains)
    };
    // Drained on BOTH paths: a refused `G1★` must not leave a width behind.
    let widths = take_required_signed_lifts();
    built.map(|(goal, texts)| (goal, texts, widths))
}

fn build_canonical_under_requires_inner(
    q_body: &Expr,
    eligible: &[(&HypothesisInput, SynExpr, Vec<String>)],
    param_types: &[(&str, &str)],
    vars: &[String],
    var_domains: &BTreeMap<String, Domain>,
) -> Result<(Expr, Vec<String>), String> {
    let mut texts: Vec<String> = Vec::with_capacity(eligible.len());
    let mut bodies: Vec<Expr> = Vec::with_capacity(eligible.len());
    for (hyp, ast, _) in eligible {
        let lifted = lift_hypothesis_source(ast, param_types).map_err(|reason| {
            format!(
                "`requires` #{} (`{}`) has no lifted reading: {reason}",
                hyp.contract_index, hyp.canonical_text
            )
        })?;
        let lifted_ast: SynExpr = syn::parse_str(&lifted).map_err(|e| {
            format!(
                "internal: the lifted reading `{lifted}` of `requires` #{} does not parse: {e}",
                hyp.contract_index
            )
        })?;
        let body = elaborate_prop_multi(&lifted_ast, vars, 0, var_domains).map_err(|reason| {
            format!(
                "`requires` #{} (`{lifted}`) is outside the lifted fragment: {reason}",
                hyp.contract_index
            )
        })?;
        texts.push(lifted);
        bodies.push(body);
    }
    let n = u32::try_from(bodies.len())
        .map_err(|_| "too many `requires` clauses to carry as hypotheses".to_string())?;
    let mut body = q_body.lift(n);
    for (j, t) in bodies.iter().enumerate().rev() {
        let shift = u32::try_from(j).unwrap_or(u32::MAX);
        body = Expr::pi(BinderInfo::Default, t.lift(shift), body);
    }
    let goal = close_over_multi(vars, body, var_domains)?;
    Ok((goal, texts))
}

/// Trust (OR-A1, Inc 1a): the LIFTED spelling `T_j` of one `E-allow` clause —
/// every integer parameter atom `x` rewritten to `(x as nat)` (unsigned
/// carrier) or `(x as int)` (signed carrier), every integer literal written
/// unsuffixed (a suffix, when present, already had to NAME the comparison's
/// carrier, so dropping it changes no value), and every `bool` atom left as it
/// is (a `bool` has no lift: its Clean reading is its mathematical reading).
///
/// Defined ONLY on the output of [`hypothesis_allow_listed`]; anything else is
/// an `Err`, never an approximation. On that fragment each rewrite is an exact
/// order-preserving injection from the lift table, so `T_j` holds of a binder
/// assignment exactly when the charged proposition does — which is the whole
/// content of the kernel-canonical link.
fn lift_hypothesis_source(ast: &SynExpr, params: &[(&str, &str)]) -> Result<String, String> {
    match ast {
        SynExpr::Paren(p) => Ok(format!("({})", lift_hypothesis_source(&p.expr, params)?)),
        SynExpr::Unary(u) if matches!(u.op, syn::UnOp::Not(_)) => {
            Ok(format!("!({})", lift_hypothesis_source(&u.expr, params)?))
        }
        SynExpr::Binary(b) if matches!(b.op, BinOp::And(_) | BinOp::Or(_)) => Ok(format!(
            "({}) {} ({})",
            lift_hypothesis_source(&b.left, params)?,
            binary_op_spelling(&b.op),
            lift_hypothesis_source(&b.right, params)?
        )),
        SynExpr::Binary(b)
            if matches!(
                b.op,
                BinOp::Eq(_) | BinOp::Ne(_) | BinOp::Lt(_) | BinOp::Le(_) | BinOp::Gt(_)
                    | BinOp::Ge(_)
            ) =>
        {
            let carrier = allow_param_carrier(&b.left, params)
                .or_else(|| allow_param_carrier(&b.right, params))
                .ok_or_else(|| {
                    "a comparison with no parameter operand has no carrier to lift from"
                        .to_string()
                })?;
            let Some(math) = lifted_math_ty(carrier)? else {
                // `bool`: nothing to lift.
                return Ok(quote::quote!(#ast).to_string());
            };
            Ok(format!(
                "{} {} {}",
                lift_hypothesis_operand(&b.left, params, math)?,
                binary_op_spelling(&b.op),
                lift_hypothesis_operand(&b.right, params, math)?
            ))
        }
        SynExpr::Lit(l) if matches!(&l.lit, Lit::Bool(_)) => Ok(quote::quote!(#ast).to_string()),
        SynExpr::Path(_) | SynExpr::Field(_) => match allow_param_carrier(ast, params) {
            Some("bool") => Ok(quote::quote!(#ast).to_string()),
            _ => Err("a bare operand that is not a `bool` parameter row".to_string()),
        },
        _ => Err("it is outside the arithmetic-free fragment the lifted reading is defined on"
            .to_string()),
    }
}

/// One comparison operand of [`lift_hypothesis_source`], at the math type its
/// comparison's carrier lifts to.
fn lift_hypothesis_operand(
    e: &SynExpr,
    params: &[(&str, &str)],
    math: MathTy,
) -> Result<String, String> {
    match e {
        SynExpr::Paren(p) => lift_hypothesis_operand(&p.expr, params, math),
        SynExpr::Path(_) | SynExpr::Field(_) => {
            let name = atom_var_name(e)
                .ok_or_else(|| "an operand is not a parameter row".to_string())?;
            if allow_param_carrier(e, params).is_none() {
                return Err(format!("`{name}` is not a parameter row of this function"));
            }
            Ok(format!("({name} as {})", math.spelling()))
        }
        SynExpr::Lit(l) => match &l.lit {
            Lit::Int(i) => Ok(i.base10_digits().to_string()),
            _ => Err("a comparison operand is a literal outside the integer fragment".to_string()),
        },
        _ => Err("a comparison operand is outside the arithmetic-free fragment".to_string()),
    }
}

/// The math type a clause carrier lifts to on the hypothesis side, `None` for
/// `bool` (no lift). Read through the SAME binder-type table the goal's binders
/// are typed from ([`Domain::from_binding_ty`]); whether the lift row itself
/// exists (a pointer-sized carrier has none) is decided later by [`lift_for`],
/// which refuses rather than guesses.
fn lifted_math_ty(carrier: &str) -> Result<Option<MathTy>, String> {
    match Domain::from_binding_ty(carrier) {
        Some(Domain::Bool) => Ok(None),
        Some(Domain::Machine(_) | Domain::U128 | Domain::USize(_) | Domain::Nat) => {
            Ok(Some(MathTy::Nat))
        }
        Some(Domain::Signed(_) | Domain::ISize(_) | Domain::Int) => Ok(Some(MathTy::Int)),
        Some(other) => Err(format!("the carrier `{}` has no lifted reading", other.rust_name())),
        None => Err(format!("`{carrier}` is not a clause binder type")),
    }
}

/// `E-allow` (design revision 2 §2.3): the arithmetic-free syntactic fragment a
/// `requires` clause must be inside before it may be carried as a kernel
/// HYPOTHESIS.
///
/// This is an ALLOW-list and only an allow-list: there is no deny-list to keep
/// in sync with the elaborator, and it must not rely on the elaborator
/// continuing to refuse anything. Admitted: parentheses; the connectives
/// `&&`, `||`, `!`; the comparisons `==`, `!=`, `<`, `<=`, `>`, `>=`; a bare
/// parameter (or depth-1 field) row; an integer literal that is
/// unsuffixed or suffixed with the comparison's own carrier; `true`/`false`.
/// Refused, and therefore OMITTED (which only makes the goal harder): every
/// arithmetic and bit operator, unary minus, casts, calls, method calls,
/// indexing, blocks, `if`/`match`, macros, floats, and a comparison with no
/// parameter operand to fix its carrier.
///
/// The exclusion of arithmetic is the false-accept guard, not a convenience.
/// Clean reads `+` on a `UIntN` as WRAPPING; the solver charges callers the
/// mathematical reading (`trust-vcgen`). For `requires a + b > 10` the two
/// readings disagree at `a = u64::MAX, b = 1`, so `F_R ⇏ P_R` and the clause
/// can never be a hypothesis, however provable the theorem looks.
fn hypothesis_allow_listed(ast: &SynExpr, params: &[(&str, &str)]) -> Result<(), String> {
    allow_prop_node(ast, params)
}

/// The Rust carrier this atom is bound at, if it is a parameter row.
///
/// Peels `Paren` the way [`allow_operand_node`] does. Without that, the
/// canonical spelling `(a) < (b)` yields no carrier from either side and is
/// omitted with "a comparison with no parameter operand", a reason that names
/// the wrong cause.
fn allow_param_carrier<'a>(e: &SynExpr, params: &'a [(&str, &str)]) -> Option<&'a str> {
    let mut node = e;
    while let SynExpr::Paren(p) = node {
        node = &p.expr;
    }
    let name = atom_var_name(node)?;
    params.iter().find(|(n, _)| *n == name).map(|(_, t)| *t)
}

/// A Bool-sorted (proposition) position of the allow-list.
fn allow_prop_node(e: &SynExpr, params: &[(&str, &str)]) -> Result<(), String> {
    match e {
        SynExpr::Paren(p) => allow_prop_node(&p.expr, params),
        SynExpr::Unary(u) if matches!(u.op, syn::UnOp::Not(_)) => {
            // `!` over a Bool-sorted node only. `!x` on an integer is Rust's
            // bitwise NOT, which is arithmetic, and is refused here.
            allow_prop_node(&u.expr, params)
        }
        SynExpr::Binary(b) if matches!(b.op, BinOp::And(_) | BinOp::Or(_)) => {
            allow_prop_node(&b.left, params)?;
            allow_prop_node(&b.right, params)
        }
        SynExpr::Binary(b)
            if matches!(
                b.op,
                BinOp::Eq(_) | BinOp::Ne(_) | BinOp::Lt(_) | BinOp::Le(_) | BinOp::Gt(_)
                    | BinOp::Ge(_)
            ) =>
        {
            // The STRUCTURAL check runs before the carrier check so the
            // diagnostic names the operator that actually caused the omission
            // (`a + b > 10` must say `+`, not "no parameter operand").
            let carrier = allow_param_carrier(&b.left, params)
                .or_else(|| allow_param_carrier(&b.right, params));
            allow_operand_node(&b.left, params, carrier)?;
            allow_operand_node(&b.right, params, carrier)?;
            if carrier.is_none() {
                return Err(
                    "a comparison with no parameter operand has no carrier to fix its reading"
                        .to_string(),
                );
            }
            Ok(())
        }
        SynExpr::Lit(l) if matches!(&l.lit, Lit::Bool(_)) => Ok(()),
        SynExpr::Path(_) | SynExpr::Field(_) => match allow_param_carrier(e, params) {
            Some("bool") => Ok(()),
            Some(other) => Err(format!(
                "a bare `{other}` operand is not a proposition; compare it instead"
            )),
            None => Err("it names something that is not a parameter row".to_string()),
        },
        SynExpr::Binary(b) => Err(format!(
            "it uses the operator `{}`, which is outside the arithmetic-free fragment on which \
             the Clean reading and the reading callers are charged provably agree",
            binary_op_spelling(&b.op)
        )),
        SynExpr::Unary(_) => Err(
            "it uses a unary operator other than `!`, which is outside the arithmetic-free \
             fragment"
                .to_string(),
        ),
        SynExpr::Call(_) | SynExpr::MethodCall(_) => Err(
            "it calls a function; a call's Clean reading is not pinned to the reading callers \
             are charged"
                .to_string(),
        ),
        SynExpr::Cast(_) => Err("it contains a cast".to_string()),
        _ => Err("it is outside the arithmetic-free `requires`-as-hypothesis fragment".to_string()),
    }
}

/// A comparison-operand position of the allow-list, at the atom's carrier.
fn allow_operand_node(
    e: &SynExpr,
    params: &[(&str, &str)],
    carrier: Option<&str>,
) -> Result<(), String> {
    match e {
        SynExpr::Paren(p) => allow_operand_node(&p.expr, params, carrier),
        SynExpr::Path(_) | SynExpr::Field(_) => match (allow_param_carrier(e, params), carrier) {
            (Some(ty), Some(carrier)) if ty != carrier => Err(format!(
                "its operands are at different carriers (`{ty}` and `{carrier}`)"
            )),
            (Some(_), _) => Ok(()),
            (None, _) => {
                Err("an operand names something that is not a parameter row".to_string())
            }
        },
        SynExpr::Lit(l) => match (&l.lit, carrier) {
            // An unsuffixed literal adopts the comparison's carrier; a suffixed
            // one must SAY that carrier. `Domain::numeral` still fails closed on
            // an out-of-range value, so no in-range claim is made here.
            (Lit::Int(i), _) if i.suffix().is_empty() => Ok(()),
            (Lit::Int(i), Some(carrier)) if i.suffix() == carrier => Ok(()),
            (Lit::Int(i), Some(carrier)) => Err(format!(
                "a literal suffixed `{}` is compared at carrier `{carrier}`",
                i.suffix()
            )),
            (Lit::Int(i), None) => Err(format!(
                "a literal suffixed `{}` has no parameter operand to agree with",
                i.suffix()
            )),
            (Lit::Bool(_), Some("bool")) => Ok(()),
            _ => Err("it compares against a literal outside the integer/bool fragment".to_string()),
        },
        SynExpr::Binary(b) => Err(format!(
            "it uses the operator `{}`, which is outside the arithmetic-free fragment on which \
             the Clean reading and the reading callers are charged provably agree",
            binary_op_spelling(&b.op)
        )),
        // A negative literal bound (`x >= -5`) is the one unary form an author
        // writes on purpose. It is still refused — `Formula::Int(-5)` renders as
        // the token `-5`, and admitting it needs the same negative-numeral range
        // argument the carrier map has not been measured for — but the reason
        // must NAME it, not blame "a unary operator" the author never typed as
        // one.
        SynExpr::Unary(u)
            if matches!(u.op, syn::UnOp::Neg(_)) && matches!(&*u.expr, SynExpr::Lit(_)) =>
        {
            Err(
                "it compares against a NEGATIVE literal, which this lane does not carry as a \
                 hypothesis yet; state the bound with a non-negative literal, or leave the clause \
                 to be charged at the call site as it already is"
                    .to_string(),
            )
        }
        SynExpr::Unary(_) => Err(
            "a comparison operand uses a unary operator, which is outside the arithmetic-free \
             fragment"
                .to_string(),
        ),
        SynExpr::Call(_) | SynExpr::MethodCall(_) => Err(
            "a comparison operand calls a function; a call's Clean reading is not pinned to the \
             reading callers are charged"
                .to_string(),
        ),
        SynExpr::Cast(_) => Err("a comparison operand contains a cast".to_string()),
        _ => Err(
            "a comparison operand is outside the arithmetic-free fragment (only a parameter, a \
             depth-1 field of one, or a literal is admitted)"
                .to_string(),
        ),
    }
}

/// The source spelling of a binary operator, for the omission diagnostic.
fn binary_op_spelling(op: &BinOp) -> &'static str {
    match op {
        BinOp::Add(_) => "+",
        BinOp::Sub(_) => "-",
        BinOp::Mul(_) => "*",
        BinOp::Div(_) => "/",
        BinOp::Rem(_) => "%",
        BinOp::BitAnd(_) => "&",
        BinOp::BitOr(_) => "|",
        BinOp::BitXor(_) => "^",
        BinOp::Shl(_) => "<<",
        BinOp::Shr(_) => ">>",
        // Reachable: `a < (b && c)` puts a logical operator in an OPERAND
        // position, and a chained comparison puts a comparison there. An
        // omission reason that named no operator at all was the alternative.
        BinOp::And(_) => "&&",
        BinOp::Or(_) => "||",
        BinOp::Eq(_) => "==",
        BinOp::Ne(_) => "!=",
        BinOp::Lt(_) => "<",
        BinOp::Le(_) => "<=",
        BinOp::Gt(_) => ">",
        BinOp::Ge(_) => ">=",
        _ => "an unsupported operator",
    }
}

/// Whether a clause AST mentions the reserved `result` identifier anywhere a
/// clause VARIABLE can occur (same traversal as [`rewrite_result_to`]; a call's
/// callee path is a function identity, not a variable).
fn mentions_result(e: &SynExpr) -> bool {
    match e {
        SynExpr::Path(p) => p.path.is_ident("result"),
        SynExpr::Paren(p) => mentions_result(&p.expr),
        // `(result as nat) == f(x as nat)` MENTIONS `result`. Without this arm
        // the `_ => false` fallthrough below would answer `false`, the
        // ensures-discharge path would skip the self-substitution entirely, and
        // `result` would be ∀-closed into a generally FALSE goal.
        SynExpr::Cast(cast) => mentions_result(&cast.expr),
        SynExpr::Unary(u) => mentions_result(&u.expr),
        SynExpr::Binary(b) => mentions_result(&b.left) || mentions_result(&b.right),
        SynExpr::Call(c) => c.args.iter().any(mentions_result),
        SynExpr::MethodCall(m) => {
            mentions_result(&m.receiver) || m.args.iter().any(mentions_result)
        }
        // `result.field` — an AGGREGATE-typed return projected in the clause.
        // Seeing it here is what routes the clause to `rewrite_result_to`,
        // which refuses it by name rather than letting it drift out as an
        // unbound variable with an unhelpful message.
        SynExpr::Field(f) => mentions_result(&f.base),
        _ => false,
    }
}

fn rewrite_result_to(e: &SynExpr, replacement: &SynExpr) -> Result<SynExpr, String> {
    Ok(match e {
        SynExpr::Path(p) if p.path.is_ident("result") => replacement.clone(),
        // The twin of the `mentions_result` arm: substitute INSIDE the cast, so
        // `result as nat` becomes `self_fn(params…) as nat`. The `other =>
        // other.clone()` fallthrough below would otherwise leave `result` in
        // place as a free variable.
        SynExpr::Cast(cast) => {
            let mut cast = cast.clone();
            cast.expr = Box::new(rewrite_result_to(&cast.expr, replacement)?);
            SynExpr::Cast(cast)
        }
        SynExpr::Paren(p) => {
            let mut p = p.clone();
            p.expr = Box::new(rewrite_result_to(&p.expr, replacement)?);
            SynExpr::Paren(p)
        }
        SynExpr::Unary(u) => {
            let mut u = u.clone();
            u.expr = Box::new(rewrite_result_to(&u.expr, replacement)?);
            SynExpr::Unary(u)
        }
        SynExpr::Binary(b) => {
            let mut b = b.clone();
            b.left = Box::new(rewrite_result_to(&b.left, replacement)?);
            b.right = Box::new(rewrite_result_to(&b.right, replacement)?);
            SynExpr::Binary(b)
        }
        SynExpr::Call(c) => {
            // Rewrite arguments (a `result` may be an argument), but NOT the
            // callee identity.
            let mut c = c.clone();
            c.args = c
                .args
                .iter()
                .map(|a| rewrite_result_to(a, replacement))
                .collect::<Result<_, _>>()?;
            SynExpr::Call(c)
        }
        SynExpr::MethodCall(m) => {
            let mut m = m.clone();
            m.receiver = Box::new(rewrite_result_to(&m.receiver, replacement)?);
            m.args = m
                .args
                .iter()
                .map(|a| rewrite_result_to(a, replacement))
                .collect::<Result<_, _>>()?;
            SynExpr::MethodCall(m)
        }
        // `result.field` — the ONE dotted path that cannot be an opaque atom.
        // Every other dotted path names a PARAMETER, whose value the clause may
        // quantify over; `result` names the function's own return value, which
        // has a kernel denotation only through the E6 import. Substituting the
        // self-call under a projection would require the aggregate carrier (the
        // import returns a struct, and `.degree` of it is a `reflect_struct`
        // field access), which this increment deliberately does not build. A
        // parameter-side projection stays untouched and resolves as a variable.
        SynExpr::Field(f) if mentions_result(&f.base) => {
            return Err(
                "a projection of `result` (`result.<field>`) is outside the clause fragment: \
                 `result` denotes the function's return value through its E6 kernel import, and \
                 projecting an aggregate return needs the struct carrier, which this fragment \
                 does not build. State the fact over a function that RETURNS the field instead."
                    .to_string(),
            );
        }
        // Literals, and any other leaf, are unchanged.
        other => other.clone(),
    })
}

/// The v7/D3 tail for a MODULE-QUALIFIED callee (`spec::first`) that has no
/// facet record while the table holds a KERNEL-CHECKED Clean island definition
/// under the callee's bare last segment (`first`).
///
/// Measured 2026-09-16 (alab-rust probes p4/p5): with the island inside
/// `mod spec`, `ensures result == spec::first(a, b)` was refused with the bare
/// "no diagnostic E6 facet record exists for `spec::first`", while the
/// identical clause spelled `first(a, b)` proved — from any module, with no
/// `use`. Nothing told the author that the spelling was the whole problem.
///
/// The refusal STAYS, and this function only words it. A qualified spelling is
/// not refused as such — a Rust function IS keyed under its module-path
/// suffixes ([`spec_spellings`]), because those keys are derived from its
/// canonical def-path and evicted when two items share one. An island
/// definition has no such path of its own: it is admitted under its Clean name,
/// in Clean's one crate-wide namespace, and many island definitions (every one
/// that is specification-only) have no Rust item at all.
///
/// ONE EXCEPTION, and it is never the spelling this tail sees. When the
/// compiler materializes a Rust item for a Clean-origin def, it records the
/// SAME audited `KernelChecked` admission a SECOND time, under that item's
/// EXACT def-path (`trust_certify::clean_island::admit_clean_origin_callee_identity`,
/// joint Rust+Lean cited lane, 2026-09-15). So a definition MAY carry two
/// admitted spellings — its bare Clean name and that one def-path — and a
/// qualified clause call on the def-path elaborates. That is authority the
/// compiler's Clean-origin registry ASSERTED, not something read off the path,
/// and only the exact def-path is keyed: no `spec_spellings` suffixes are minted
/// for it. Such a spelling never reaches this function, because
/// [`first_call_facet_error`] returns at its `facets.admitted(&callee)` check
/// and this tail runs only where the callee has NO facet record at all. The
/// argument below is therefore about every OTHER qualified spelling — the ones
/// with no record, which is all this tail is ever asked to word. Accepting
/// `spec::first` here would mean deciding that the Rust-looking path denotes
/// the Clean constant `first`, and nothing at this seam can decide that: clause
/// text is not name-resolved, so `other::first` — a different Rust function
/// that merely shares the bare name — is indistinguishable from `spec::first`.
/// Stripping the qualifier would bind a clause about one function to the
/// definition of another. Hence the wording is conditional: it never asserts
/// that the path denotes the island definition.
///
/// The PRINTED text below stands unamended for the same reason: it is emitted
/// only on the no-record branch, where the callee provably is not the
/// materialized def-path, so "`{callee}` cannot be shown to denote `{bare}`" is
/// true of every spelling that reaches it, and its option (1) — write the bare
/// Clean name — is the working advice whether or not the definition also has a
/// materialized Rust item.
///
/// `None` unless the bare segment is admitted AND passes
/// [`Admission::require_kernel_check`] — a reflected Rust carrier under the
/// bare name is a Rust function, not an island definition, and gets no hint.
fn qualified_island_spelling_hint(callee: &str, facets: &FacetTable) -> Option<String> {
    let (_, bare) = callee.rsplit_once("::")?;
    let admission = facets.admitted(bare)?;
    admission.require_kernel_check().ok()?;
    Some(format!(
        ". `{callee}` is spelled as a Rust path, and a kernel-checked Clean island definition \
         IS admitted under the bare Clean name `{bare}`: an island definition is named in \
         Clean's one crate-wide namespace, whatever Rust module its island sits in, and clause \
         paths are not name-resolved, so `{callee}` cannot be shown to denote `{bare}`. \
         options: (1) if `{callee}` is that island definition, write `{bare}(..)` — the bare \
         Clean name is accepted from any module, with no `use`; (2) if `{callee}` is a \
         different Rust function that shares the name, this clause is about that function, \
         which needs its own E6 kernel admission — and consider renaming one of the two, \
         because every clause that writes `{bare}` means the island definition"
    ))
}

/// Walk the spec AST; on the first program-function call, produce the
/// facet-aware E6 diagnostic. `None` means the spec contains no calls and
/// elaboration may proceed on the ordinary path.
fn first_call_facet_error(ast: &SynExpr, facets: &FacetTable) -> Option<String> {
    match ast {
        SynExpr::Paren(p) => first_call_facet_error(&p.expr, facets),
        // A spec cast is transparent to this walk: `f(x) as nat` names `f`, and
        // an unadmitted `f` must get the refined facet diagnostic rather than
        // `elab_term`'s generic E6 backstop.
        SynExpr::Cast(cast) => first_call_facet_error(&cast.expr, facets),
        SynExpr::Unary(u) => first_call_facet_error(&u.expr, facets),
        SynExpr::Binary(b) => first_call_facet_error(&b.left, facets)
            .or_else(|| first_call_facet_error(&b.right, facets)),
        SynExpr::Call(c) => {
            let callee = callee_path(c);
            // `Some(..)` is the Option CONSTRUCTOR former, not a program
            // function — it has no facet record by design and is typed (or
            // refused) by the elaborator's own Option-carrier gate. Its
            // argument may still contain a genuine call; keep walking it.
            if callee == "Some" {
                return c.args.iter().find_map(|arg| first_call_facet_error(arg, facets));
            }
            // An ADMITTED call (certified facets + a minted kernel constant)
            // is admissible — it elaborates to the constant in `elab_term`, so
            // it must NOT produce a diagnostic here. But its ARGUMENTS may
            // themselves contain a non-admitted call, which still fails closed;
            // report the first such.
            if facets.admitted(&callee).is_some() {
                return c.args.iter().find_map(|arg| first_call_facet_error(arg, facets));
            }
            Some(match facets.get(&callee) {
                None => {
                    let mut message = format!(
                        "no diagnostic E6 facet record exists for `{callee}`; public facet \
                         findings cannot admit a call and no sealed, item-bound kernel \
                         admission exists, so the program-function call fails closed; \
                         mention the function through its operational relation instead"
                    );
                    if let Some(hint) = qualified_island_spelling_hint(&callee, facets) {
                        message.push_str(&hint);
                    }
                    message
                }
                Some(f) if !f.admissible() => format!(
                    "at least one E6 structural facet of `{callee}` is not established: \
                     {}; public facet findings are diagnostic only and no sealed, \
                     item-bound kernel admission exists, so the call fails closed",
                    f.deficits().join(", ")
                ),
                Some(_) => format!(
                    "all four public E6 structural facet findings of `{callee}` are \
                     positive, but they are diagnostic only; no sealed, item-bound \
                     kernel admission exists, so the call fails closed"
                ),
            })
        }
        SynExpr::MethodCall(m) => Some(format!(
            "method call `.{}(..)` in a spec is outside the kernel fragment: public \
             E6 facet findings are diagnostic only, and resolved item identity plus \
             a sealed, item-bound kernel admission are absent; method calls fail \
             closed, so mention the method through its operational relation instead",
            m.method
        )),
        _ => None,
    }
}

fn parse_exact_clause_vars<T>(
    spec: &str,
    var_types: &[(&str, T)],
) -> Result<(SynExpr, Vec<String>), String> {
    let ast: SynExpr = syn::parse_str(spec).map_err(|e| format!("parse error: {e}"))?;
    let vars = collect_exact_clause_vars(&ast, var_types)?;
    Ok((ast, vars))
}

fn collect_exact_clause_vars<T>(
    ast: &SynExpr,
    var_types: &[(&str, T)],
) -> Result<Vec<String>, String> {
    let mut vars = Vec::new();
    collect_vars(ast, &mut vars);
    // A bare identifier that names an ambient-admitted constant is a
    // CITATION, not a clause variable — a ZERO-ARITY one resolves to the
    // kernel constant in `elab_term`'s Path arm, and a parametered one is
    // refused there and in [`atom_domain`] with the fix named ("must be
    // applied") — so the exact-binding bijection must not demand a type for
    // it. Precedence is fail-closed and matches `elab_term`: a name the
    // caller BINDS stays a variable (params shadow admissions), so an island
    // definition can never change what an existing green clause means.
    // Outside an [`AdmissionScope`] the ambient table is empty and this
    // retains everything — the plain `elaborate_goal_typed` path is
    // byte-identical to before.
    //
    // I0: written as a loop rather than a `retain` because the consult can now
    // REFUSE — a bare identifier the caller does not bind but the compiler
    // records as a Rust binding of the specified function must not be dropped
    // from the bijection and silently resolved as a citation. Order and
    // membership are otherwise exactly what the `retain` produced.
    let mut retained = Vec::with_capacity(vars.len());
    for v in vars {
        if var_types.iter().any(|(n, _)| *n == v) || ambient_bare_admission(&v)?.is_none() {
            retained.push(v);
        }
    }
    Ok(retained)
}

/// The exact-binding bijection gate shared by [`parse_exact_typed_clause`] and
/// the quantified (E3) clause path: `var_types` must bind exactly the clause's
/// FREE identifiers — duplicates, missing names, extra names, and unsupported
/// types all fail closed. A quantifier-BOUND variable is not free, so it must
/// NOT appear in `var_types` (the caller subtracts binders before calling).
fn exact_typed_bindings(
    free_vars: &[String],
    var_types: &[(&str, &str)],
) -> Result<BTreeMap<String, Domain>, String> {
    let mut bindings = BTreeMap::new();
    for &(name, ty) in var_types {
        if name.is_empty() {
            return Err("clause variable binding has an empty name".to_string());
        }
        let domain = Domain::from_binding_ty(ty).ok_or_else(|| {
            format!(
                "unsupported clause variable type `{ty}` (supported: {})",
                E3_BINDER_TYPES.join(", ")
            )
        })?;
        if bindings.insert(name.to_string(), domain).is_some() {
            return Err(format!("duplicate clause variable binding `{name}`"));
        }
    }

    check_exact_binding_names(free_vars, &bindings)?;
    Ok(bindings)
}

fn exact_domain_bindings(
    free_vars: &[String],
    var_domains: &[(&str, Domain)],
) -> Result<BTreeMap<String, Domain>, String> {
    let mut bindings = BTreeMap::new();
    for (name, domain) in var_domains {
        if name.is_empty() {
            return Err("clause variable binding has an empty name".into());
        }
        if bindings.insert((*name).to_string(), domain.clone()).is_some() {
            return Err(format!("duplicate clause variable binding `{name}`"));
        }
    }
    check_exact_binding_names(free_vars, &bindings)?;
    Ok(bindings)
}

fn check_exact_binding_names(
    free_vars: &[String],
    bindings: &BTreeMap<String, Domain>,
) -> Result<(), String> {
    let free: BTreeSet<&str> = free_vars.iter().map(String::as_str).collect();
    let supplied: BTreeSet<&str> = bindings.keys().map(String::as_str).collect();
    let missing: Vec<&str> = free.difference(&supplied).copied().collect();
    let extra: Vec<&str> = supplied.difference(&free).copied().collect();
    if !missing.is_empty() || !extra.is_empty() {
        return Err(format!(
            "clause variable bindings are not exact (missing: [{}]; extra: [{}])",
            missing.join(", "),
            extra.join(", ")
        ));
    }

    // Per-variable domains: distinct variables may carry DIFFERENT domains
    // (e.g. `flag && x < 10` binds `flag : Bool` and `x : UInt64`). The one
    // constraint — that a single comparison's operands agree — is enforced
    // per-atom in [`atom_domain`], not here.
    Ok(())
}

/// The single domain of one atom (a comparison, equality, or bare boolean): the
/// common domain of the variables occurring in it. Distinct comparisons in a
/// `&& || !` tree may differ, but the operands of ONE comparison must share a
/// type (`x == flag` mixing `u64` and `bool` fails closed). A literal adopts the
/// atom's domain.
///
/// THE ORDER BELOW IS STRICTLY ADDITIVE (E6/E9 widening increment 8). Step 1 is
/// the pre-increment computation, unchanged and tried first, so every clause
/// that resolved before resolves identically now. Steps 2 and 3 fire only where
/// step 1 previously ENDED THE CLAUSE — at a variable-free atom (which defaulted
/// to `Nat`) and at a "mixed domains" refusal — so neither can retype a working
/// clause:
///
///  1. every free variable of the atom, call arguments included;
///  2. a VARIABLE-FREE atom takes the declared RESULT domain of the admitted
///     calls in it (see [`atom_call_result_domain`]), and only then `Nat`.
///     Before this, `result == zero_isl()` on a nullary constant function put a
///     `BitVec 64` island call under an `Eq Nat` and the ill-typed-goal gate
///     refused it — the documented f04-f09 wall;
///  3. a step-1 MIXED-DOMAIN refusal is re-examined over the atom's AMBIENT
///     operands only (see [`collect_ambient_vars`]): an argument of a call whose
///     callee declares its own parameter carriers is typed by that callee and
///     was never an operand of this comparison. `result == eq_ok_isl(machine,
///     truth)` — an island declared `(m : BitVec 64) (t : BitVec 128)` — is the
///     shape this recovers. When the ambient operands are THEMSELVES mixed, or
///     when nothing is left to type the atom, the ORIGINAL refusal stands: a
///     bare `machine == truth` across two widths has no callee to justify it and
///     is still an error.
///
/// Step 3 also takes a step-1 domain that a typed OPERAND contradicts (see
/// [`step_one_result_carrier_conflict`]). Step 1 reads a typed call's
/// ARGUMENTS, and a call's arguments need not share the carrier of what it
/// RETURNS: for `fn cursor(has: bool, fresh: bool) -> u8` the self-call and
/// `spec_cursor(has, fresh)` both return `UInt8` while every variable step 1
/// sees is a `bool`, so step 1 built `Eq Bool` over two `UInt8` terms, a goal
/// the kernel refuses as ill-typed. Taking step 3 there cannot retype a working
/// clause: the step-1 domain it replaces put a call whose declared result
/// carrier differs from it under the relation, and no such goal typechecks.
fn atom_domain(atom: &SynExpr, var_domains: &BTreeMap<String, Domain>) -> Result<Domain, String> {
    // A datatype-valued call's argument types need not equal its result type.
    // Keep the compatibility path for scalar-only clauses, but for registered
    // carriers derive the relation from AMBIENT operands and declared results,
    // leaving each call's arguments to its own telescope checks.
    let mut calls = Vec::new();
    collect_ambient_calls(atom, &mut calls);
    let registered_call = calls.iter().any(|call| {
        matches!(call_ret_domain(call), Some(Domain::RegisteredAdt(_)))
            || typed_callee_carriers(call)
                .is_some_and(|cs| matches!(cs.ret, Carrier::RegisteredAdt(_)))
    });
    let mut atom_vars = Vec::new();
    collect_vars(atom, &mut atom_vars);
    if atom_vars.iter().any(|name| matches!(var_domains.get(name), Some(Domain::RegisteredAdt(_))))
        || registered_call
    {
        let mut domain = resolved_atom_domain(atom, var_domains)?;
        collect_ambient_term_domain_evidence(atom, &mut domain)?;
        if let Some(result_domain) = atom_call_result_domain(atom)? {
            merge_term_domain_evidence(&mut domain, result_domain, "admitted call result")?;
        }
        if let Some(domain) = domain {
            check_ambient_call_result_carriers(atom, &domain)?;
            return Ok(domain);
        }
    }
    let mixed = match resolved_atom_domain_all_vars(atom, var_domains) {
        Ok(Some(dom)) => match step_one_result_carrier_conflict(atom, &dom) {
            None => return Ok(dom),
            // Step 3 decides from the ambient operands. Its own refusals are
            // the clause's: an ambient VARIABLE at step 1's domain beside the
            // contradicting call (`flag == spec(a, b)` with `spec -> u8`) fails
            // its carrier check, and callees that disagree with each other fail
            // `atom_call_result_domain`. With nothing left to decide, this
            // conflict is the refusal.
            Some(conflict) => conflict,
        },
        Ok(None) => {
            // main's C6 lane: a variable-free atom derives its domain from
            // TERM EVIDENCE, and CONFLICTING evidence refuses -- which is why
            // the collector runs FIRST and the call-result steering is only a
            // fallback for an atom the collector finds no evidence in. An
            // early return on the call result alone silently swallowed a
            // u64-callee-vs-u32-literal conflict (measured:
            // conflicting_term_domain_evidence_refuses).
            //
            // The AMBIENT collector (TG15): a typed call contributes the
            // result it declares, never evidence from inside its argument
            // list, which its own declaration types. `result == widen(g())` on
            // a nullary `-> u16` relates two `UInt16` results; reading `g`'s
            // `u8` out of `widen`'s argument refused it as mixed.
            let mut dom: Option<Domain> = None;
            collect_ambient_term_domain_evidence(atom, &mut dom)?;
            if let Some(d) = dom {
                return Ok(d);
            }
            return Ok(atom_call_result_domain(atom)?.unwrap_or(Domain::Nat));
        }
        Err(mixed) => mixed,
    };
    // `?` here, not `.ok()`: an ambient-operand disagreement is a REAL mixed
    // comparison and must surface, not be swallowed into the fallback.
    if let Some(dom) = resolved_atom_domain(atom, var_domains)? {
        check_ambient_call_result_carriers(atom, &dom)?;
        return Ok(dom);
    }
    atom_call_result_domain(atom)?.ok_or(mixed)
}

/// Relation evidence must retain explicit scalar literal suffixes without
/// confusing a typed callee's arguments with the value it returns.
fn collect_ambient_term_domain_evidence(
    e: &SynExpr,
    domain: &mut Option<Domain>,
) -> Result<(), String> {
    match e {
        SynExpr::Paren(p) => collect_ambient_term_domain_evidence(&p.expr, domain),
        SynExpr::Unary(u) => collect_ambient_term_domain_evidence(&u.expr, domain),
        SynExpr::Binary(b) => {
            collect_ambient_term_domain_evidence(&b.left, domain)?;
            collect_ambient_term_domain_evidence(&b.right, domain)
        }
        SynExpr::Call(call) if typed_callee_carriers(call).is_some() => {
            if let Some(found) = atom_call_result_domain(e)? {
                merge_term_domain_evidence(domain, found, "admitted call result")?;
            }
            Ok(())
        }
        leaf => collect_term_domain_evidence(leaf, domain),
    }
}

/// Merge one piece of term-derived domain evidence into `dom`, failing closed
/// on a conflict: the operands of a single comparison must share a type, and
/// two terms that pin different domains cannot be reconciled by preferring
/// either — whichever loses would elaborate at the wrong carrier.
fn merge_term_domain_evidence(
    dom: &mut Option<Domain>,
    found: Domain,
    source: &str,
) -> Result<(), String> {
    match dom {
        None => {
            *dom = Some(found);
            Ok(())
        }
        Some(existing) if *existing == found => Ok(()),
        Some(existing) => Err(format!(
            "mixed domains in one comparison ({existing:?} and {found:?} from {source}) — the \
             operands of a single comparison must share a type"
        )),
    }
}

/// Walk one atom for the domain its TERMS pin down. Two term shapes carry
/// evidence:
///
/// * a call to an ADMITTED callee whose [`Admission`] records a return domain
///   — read from the same ambient table `elab_term`'s call arm consults, so
///   the domain used to type the comparison is the domain of the kernel
///   constant that will appear in it;
/// * a SUFFIXED integer literal (`42u64`) — the source spelled the type.
///
/// Everything else contributes nothing: an unsuffixed literal adopts the
/// atom's domain exactly as before, an admission without a recorded return
/// domain keeps the pre-existing default, and a non-admitted call fails
/// closed later regardless of the domain chosen here. Conflicting evidence
/// fails closed ([`merge_term_domain_evidence`]); a literal suffix outside
/// the supported domain set fails closed with the fix rather than being
/// silently dropped.
fn collect_term_domain_evidence(e: &SynExpr, dom: &mut Option<Domain>) -> Result<(), String> {
    match e {
        SynExpr::Paren(p) => collect_term_domain_evidence(&p.expr, dom),
        SynExpr::Unary(u) => collect_term_domain_evidence(&u.expr, dom),
        SynExpr::Binary(b) => {
            collect_term_domain_evidence(&b.left, dom)?;
            collect_term_domain_evidence(&b.right, dom)
        }
        SynExpr::Lit(l) => {
            if let Lit::Int(i) = &l.lit {
                let suffix = i.suffix();
                if !suffix.is_empty() {
                    let found = Domain::from_binding_ty(suffix).ok_or_else(|| {
                        format!(
                            "unsupported literal suffix `{suffix}` in a spec atom; drop the \
                             suffix (an unsuffixed literal adopts the comparison's domain) or \
                             bind the value through a typed clause variable"
                        )
                    })?;
                    merge_term_domain_evidence(dom, found, &format!("literal suffix `{suffix}`"))?;
                }
            }
            Ok(())
        }
        SynExpr::Call(c) => {
            if let SynExpr::Path(p) = &*c.func {
                let callee = path_spelling(&p.path);
                // I0: STEERING ONLY (see [`ambient_admission`]). Choosing the
                // domain a term is built at cannot bind a name; the deciding
                // consult in `elab_term`'s call arm refuses a shadowed callee
                // before any goal built here is submitted.
                if let Some(found) =
                    ambient_admission(&callee).and_then(|a| a.return_domain().cloned())
                {
                    merge_term_domain_evidence(dom, found, &format!("admitted callee `{callee}`"))?;
                }
            }
            // Argument terms are elaborated at the atom's domain (the admitted
            // fragment is single-domain), so evidence found inside them
            // constrains the same choice.
            for arg in &c.args {
                collect_term_domain_evidence(arg, dom)?;
            }
            Ok(())
        }
        SynExpr::MethodCall(m) => {
            collect_term_domain_evidence(&m.receiver, dom)?;
            for arg in &m.args {
                collect_term_domain_evidence(arg, dom)?;
            }
            Ok(())
        }
        _ => Ok(()),
    }
}

/// Elaborate a proposition where each atom takes its own domain (from
/// [`atom_domain`]). Connectives combine atoms of possibly-different domains,
/// so `flag && x < 10` elaborates over `Bool` and `UInt64` together. For a
/// single-domain clause this produces exactly the same term as
/// [`elaborate_prop`]; the difference shows only when domains are mixed across
/// connectives.
fn elaborate_prop_multi(
    ast: &SynExpr,
    vars: &[String],
    offset: u32,
    var_domains: &BTreeMap<String, Domain>,
) -> Result<Expr, String> {
    match ast {
        SynExpr::Paren(p) => elaborate_prop_multi(&p.expr, vars, offset, var_domains),
        SynExpr::Unary(u) if matches!(u.op, syn::UnOp::Not(_)) => Ok(Expr::app(
            Expr::const_(Name::interned("Not"), vec![]),
            elaborate_prop_multi(&u.expr, vars, offset, var_domains)?,
        )),
        SynExpr::Binary(b) if matches!(b.op, BinOp::And(_)) => Ok(connective(
            "And",
            elaborate_prop_multi(&b.left, vars, offset, var_domains)?,
            elaborate_prop_multi(&b.right, vars, offset, var_domains)?,
        )),
        SynExpr::Binary(b) if matches!(b.op, BinOp::Or(_)) => Ok(connective(
            "Or",
            elaborate_prop_multi(&b.left, vars, offset, var_domains)?,
            elaborate_prop_multi(&b.right, vars, offset, var_domains)?,
        )),
        SynExpr::Binary(b) if matches!(b.op, BinOp::Ne(_)) => {
            elaborate_prop_multi(&ne_as_not_eq(b), vars, offset, var_domains)
        }
        SynExpr::Lit(l) if matches!(&l.lit, Lit::Bool(_)) => {
            let value = matches!(&l.lit, Lit::Bool(bb) if bb.value);
            Ok(Expr::const_(Name::interned(if value { "True" } else { "False" }), vec![]))
        }
        // A bare identifier — or a dotted path naming a `bool` FIELD — is a
        // proposition only for a `bool` binding.
        SynExpr::Path(_) | SynExpr::Field(_) => {
            let dom = atom_domain(ast, var_domains)?;
            if !dom.is_bool() {
                return Err("a bare identifier is a proposition only for a `bool` binding".into());
            }
            let v = elab_term(ast, vars, offset, var_domains, &dom)?;
            Ok(dom.eq(v, dom.bool_lit(true)?))
        }
        SynExpr::Binary(b) => {
            // BOOL-CARRIER EQUALITY. When a side is a `bool`-valued form the
            // single-`Domain` lane cannot express — a nested comparison, a
            // boolean connective, or a call to an admitted `-> bool` function —
            // the RELATION is an `Eq Bool` while the OPERANDS inside each side
            // keep their own arithmetic domain. Splitting the two is what makes
            // `result == (a <= b)` and `result == le_isl(a, b)` statable; before
            // it, `atom_domain` reported the nested comparison's own operands as
            // a mixed-domain comparison and the clause never reached the kernel.
            //
            // Ordering is not `==`-only by accident: `!=` has already been
            // desugared to `!(a == b)` by the `Ne` arm above, and an ORDERING
            // comparison of two `bool`s stays refused — `bool` has no order, and
            // the existing guard below says so.
            // OPTION-CARRIER EQUALITY (checked-arith spec §3.3). When a side
            // is a call admitted with an `Option<iN>` return domain, the
            // relation is `Eq (Option (BitVec N))` and each side elaborates as
            // an Option operand — a `Some(..)`/`None` constructor or another
            // same-carrier admitted call — while the operands INSIDE each side
            // keep their own signed domain. A bare `Some(..)`/`None` with NO
            // admitted-call side has no carrier to bind to and fails closed
            // below (`elab_term` names the reason); ORDERING over an Option is
            // refused like `bool`.
            let option_width = call_option_ret_width(&b.left)
                .or_else(|| call_option_ret_width(&b.right));
            if let Some(width) = option_width {
                if matches!(b.op, BinOp::Eq(_)) {
                    let l = elab_option_term(&b.left, vars, offset, width, var_domains)?;
                    let r = elab_option_term(&b.right, vars, offset, width, var_domains)?;
                    return Ok(Domain::OptionSigned(width).eq(l, r));
                }
                if matches!(b.op, BinOp::Le(_) | BinOp::Lt(_) | BinOp::Ge(_) | BinOp::Gt(_)) {
                    return Err("`Option` values are not ordered (use `==` or `!=`)".into());
                }
            }
            let decided_side =
                decided_bool_form(&b.left, var_domains) || decided_bool_form(&b.right, var_domains);
            if matches!(b.op, BinOp::Eq(_)) && decided_side {
                let l = elab_bool_term(&b.left, vars, offset, var_domains)?;
                let r = elab_bool_term(&b.right, vars, offset, var_domains)?;
                return Ok(Domain::Bool.eq(l, r));
            }
            // An ORDERING comparison with a decided `bool` side is refused for
            // the same reason a `bool` binding is — and BEFORE `atom_domain`
            // runs, so the diagnostic names the real cause instead of blaming a
            // mixed comparison that does not exist (`result <= (a <= b)` has two
            // `Bool` operands, not a `Bool` and an `i64`).
            if matches!(b.op, BinOp::Le(_) | BinOp::Lt(_) | BinOp::Ge(_) | BinOp::Gt(_))
                && decided_side
            {
                return Err("`bool` values are not ordered (use `==` or `!=`)".into());
            }
            // THE MATH RELATION ROW (nat-lift design §3.4). Fires only in
            // `ProofLift` mode and only for an atom that syntactically carries
            // a cast — which is an atom the pre-existing path REFUSES, so no
            // clause that elaborates today can be retyped by it. Without this,
            // `atom_domain` would resolve `clamp_nat(c as nat, d as nat) <= (d
            // as nat)` over the variables `c`/`d` and build the relation at
            // `u32`, putting a `Nat` term under `UInt32.toNat` — well-formed
            // as a term, ill-typed as a proposition.
            if let Some(relation) = elab_math_relation(b, vars, offset, var_domains)? {
                return Ok(relation);
            }
            let dom = atom_domain(ast, var_domains)?;
            if matches!(dom, Domain::RegisteredAdt(_)) && !matches!(b.op, BinOp::Eq(_)) {
                return Err(dom.registered_operation_refusal("ordering"));
            }
            if dom.is_bool()
                && matches!(b.op, BinOp::Le(_) | BinOp::Lt(_) | BinOp::Ge(_) | BinOp::Gt(_))
            {
                return Err("`bool` values are not ordered (use `==` or `!=`)".into());
            }
            let l = elab_term(&b.left, vars, offset, var_domains, &dom)?;
            let r = elab_term(&b.right, vars, offset, var_domains, &dom)?;
            Ok(match b.op {
                BinOp::Eq(_) => dom.eq(l, r),
                BinOp::Le(_) => dom.cmp("le", l, r),
                BinOp::Lt(_) => dom.cmp("lt", l, r),
                BinOp::Ge(_) => dom.cmp("le", r, l),
                BinOp::Gt(_) => dom.cmp("lt", r, l),
                _ => return Err("comparison op must be one of == != <= < >= >".into()),
            })
        }
        // A call to an admitted `-> bool` function IS a proposition, read as
        // `f(a, b) = true` — the same reading the bare-`Path` `bool` arm gives a
        // boolean binding. Every other call still fails closed (E6): the
        // diagnostic is domain-independent, so reuse the single-domain arm.
        SynExpr::Call(c) if call_ret_domain(c).is_some_and(|d| d.is_bool()) => {
            let arg_dom = atom_domain(ast, var_domains)?;
            let v = elab_term(ast, vars, offset, var_domains, &arg_dom)?;
            Ok(Domain::Bool.eq(v, Domain::Bool.bool_lit(true)?))
        }
        SynExpr::Call(_) | SynExpr::MethodCall(_) => {
            elaborate_prop(ast, vars, offset, &Domain::Nat)
        }
        _ => Err("predicate must be a comparison or a connective (&& || !)".into()),
    }
}

/// Close a body over `vars`, binding EACH variable with its own domain's type
/// (`∀ (flag : Bool) (x : UInt64), …`). The binders are wrapped inner-to-outer,
/// so iteration is reversed: the last variable is the innermost binder
/// (`bvar 0`), matching [`elab_term`]'s de Bruijn convention.
fn close_over_multi(
    vars: &[String],
    body: Expr,
    var_domains: &BTreeMap<String, Domain>,
) -> Result<Expr, String> {
    let mut goal = body;
    for v in vars.iter().rev() {
        let d = var_domains.get(v).ok_or_else(|| format!("unbound variable `{v}`"))?;
        goal = Expr::pi(BinderInfo::Default, d.ty(), goal);
    }
    Ok(goal)
}

/// [`close_over_multi`] for a λ-body (the monitor / its proof) rather than a
/// ∀-goal: binds each variable with its own domain's type.
fn close_over_lam_multi(
    vars: &[String],
    body: Expr,
    var_domains: &BTreeMap<String, Domain>,
) -> Result<Expr, String> {
    let mut e = body;
    for v in vars.iter().rev() {
        let d = var_domains.get(v).ok_or_else(|| format!("unbound variable `{v}`"))?;
        e = Expr::lam(BinderInfo::Default, d.ty(), e);
    }
    Ok(e)
}

/// Every variable maps to the single `dom` — the uniform map a single-domain
/// [`certify_monitor`] call threads through the (otherwise multi-domain) monitor
/// lane, so its behaviour is byte-identical to the pre-multi-domain code.
fn uniform_var_domains(vars: &[String], dom: &Domain) -> BTreeMap<String, Domain> {
    vars.iter().map(|v| (v.clone(), dom.clone())).collect()
}

/// Elaborate a `requires(pre) ensures(post)` contract into `∀ vars, pre → post`
/// over unbounded `Nat`: the precondition is an ASSUMED hypothesis and the
/// postcondition must be PROVED. `post` is elaborated at offset 1 because it
/// sits under the extra `pre`-arrow binder.
pub fn elaborate_contract(requires: &str, ensures: &str) -> Result<Expr, String> {
    elaborate_contract_in(requires, ensures, &Domain::Nat)
}

/// Build the same mathematical contract statement over an explicit closed
/// arithmetic domain.
///
/// A machine domain selects the corresponding fixed-width wrapping carrier,
/// but this remains a statement constructor only. It does not bind source
/// variables, a function, or an exact typed Trust-IR obligation, and therefore
/// grants no Rust VC or check-elision authority.
pub fn elaborate_contract_in(requires: &str, ensures: &str, dom: &Domain) -> Result<Expr, String> {
    if matches!(dom, Domain::RegisteredAdt(_)) {
        return Err("registered datatype contracts require current-environment validation; use elaborate_goal_with_domains for an implication or elaborate_ensures_with_domains for the admitted function result".into());
    }
    let pre_ast: SynExpr = syn::parse_str(requires).map_err(|e| format!("requires parse: {e}"))?;
    let post_ast: SynExpr = syn::parse_str(ensures).map_err(|e| format!("ensures parse: {e}"))?;
    let mut vars = Vec::new();
    collect_vars(&pre_ast, &mut vars);
    collect_vars(&post_ast, &mut vars);
    let uniform = uniform_var_domains(&vars, dom);
    let pre = elaborate_prop_with_uniform(&pre_ast, &vars, 0, dom, &uniform)?;
    let post = elaborate_prop_with_uniform(&post_ast, &vars, 1, dom, &uniform)?;
    Ok(close_over(&vars, Expr::pi(BinderInfo::Default, pre, post), dom))
}

/// The executable, language-independent shape of a certified monitor.
///
/// This raw syntax is public for inspection, testing, and non-authoritative
/// evaluation. Consumers can construct it directly, so it is never evidence of
/// certification by itself; only the sealed [`CertifiedMonitor`] carrier (and a
/// compiler-private binding derived from it) conveys kernel-checked provenance.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RuntimeMonitorExpr {
    Var(String),
    Zero,
    /// A non-negative integer literal. In range for the monitor's domain by
    /// construction: the paired kernel goal is elaborated first (via
    /// `Domain::numeral`, which rejects an out-of-range literal), so a monitor
    /// is only ever minted for a literal the type admits.
    Lit(u128),
    Add(Box<Self>, Box<Self>),
    Sub(Box<Self>, Box<Self>),
    Mul(Box<Self>, Box<Self>),
    Div(Box<Self>, Box<Self>),
    Rem(Box<Self>, Box<Self>),
    BitAnd(Box<Self>, Box<Self>),
    BitOr(Box<Self>, Box<Self>),
    BitXor(Box<Self>, Box<Self>),
    Eq(Box<Self>, Box<Self>),
    Le(Box<Self>, Box<Self>),
    Lt(Box<Self>, Box<Self>),
    Ge(Box<Self>, Box<Self>),
    Gt(Box<Self>, Box<Self>),
    And(Box<Self>, Box<Self>),
    Or(Box<Self>, Box<Self>),
    Not(Box<Self>),
}

/// Arithmetic carrier to which the executable monitor is bound.  Fixed-width
/// variants use Rust wrapping semantics. `Nat` evaluation is checked because
/// the helper's `u128` test representation cannot silently approximate an
/// unbounded mathematical value.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RuntimeMonitorDomain {
    Nat,
    U8,
    U16,
    U32,
    U64,
    U128,
    I8,
    I16,
    I32,
    I64,
    I128,
    USize16,
    USize32,
    USize64,
    ISize16,
    ISize32,
    ISize64,
    /// `bool` — a 1-bit carrier, so `normalize` keeps arguments in `{0, 1}`.
    /// Only equality/connective monitors reach it (no arithmetic).
    Bool,
}

impl RuntimeMonitorDomain {
    fn bits(self) -> Option<u32> {
        match self {
            Self::Nat => None,
            Self::U8 => Some(8),
            Self::U16 => Some(16),
            Self::U32 => Some(32),
            Self::U64 => Some(64),
            Self::U128 | Self::I128 => Some(128),
            Self::I8 => Some(8),
            Self::I16 | Self::USize16 | Self::ISize16 => Some(16),
            Self::I32 | Self::USize32 | Self::ISize32 => Some(32),
            Self::I64 | Self::USize64 | Self::ISize64 => Some(64),
            Self::Bool => Some(1),
        }
    }

    fn is_signed(self) -> bool {
        matches!(
            self,
            Self::I8
                | Self::I16
                | Self::I32
                | Self::I64
                | Self::I128
                | Self::ISize16
                | Self::ISize32
                | Self::ISize64
        )
    }

    fn source_name(self) -> &'static str {
        match self {
            Self::Nat => "nat",
            Self::U8 => "u8",
            Self::U16 => "u16",
            Self::U32 => "u32",
            Self::U64 => "u64",
            Self::U128 => "u128",
            Self::I8 => "i8",
            Self::I16 => "i16",
            Self::I32 => "i32",
            Self::I64 => "i64",
            Self::I128 => "i128",
            Self::USize16 => "usize16",
            Self::USize32 => "usize32",
            Self::USize64 => "usize64",
            Self::ISize16 => "isize16",
            Self::ISize32 => "isize32",
            Self::ISize64 => "isize64",
            Self::Bool => "bool",
        }
    }

    fn normalize(self, value: u128) -> Result<u128, String> {
        let Some(bits) = self.bits() else { return Ok(value) };
        let outside = bits < 128 && value > bit_mask(bits);
        if outside {
            if self == Self::Bool {
                return Err(format!("monitor argument {value} is outside the bool carrier"));
            }
            return Err(format!(
                "monitor argument {value} is outside the `{}` carrier",
                self.source_name()
            ));
        }
        Ok(value)
    }

    fn wrapping_bin(self, lhs: u128, rhs: u128, op: ArithOp) -> Result<u128, String> {
        if self == Self::Bool {
            return Err("monitor runtime: arithmetic is not supported for `bool`".into());
        }
        if self.is_signed() && matches!(op, ArithOp::Div | ArithOp::Rem) {
            return Err(format!(
                "monitor runtime: signed division/remainder is not implemented for `{}`",
                self.source_name()
            ));
        }
        match self.bits() {
            None => match op {
                // `/` and `%` are only ever built with a positive-literal
                // divisor (the elaborator gate), so `rhs == 0` here means a
                // monitor was hand-built outside the certified path — fail
                // rather than panic. The check is an arm of the SAME match that
                // divides: a separate `matches!(op, Div | Rem)` guard ahead of
                // the match reads the discriminant a second time, and the
                // verifier does not relate the two reads, so it refuted the
                // division at `rhs = 0` with the guard in place (measured
                // 2026-09-13 on `dff2b22d1`; the in-match arm proves).
                ArithOp::Div | ArithOp::Rem if rhs == 0 => {
                    return Err("monitor runtime: division or remainder by zero".into());
                }
                // Nat: `+`/`*` are exact (checked against the u128 test
                // representation); `-` is TRUNCATED (`Nat.sub`, saturating at 0),
                // never underflows; `/`/`%` are exact (divisor > 0); bitwise
                // ops combine the bit-patterns directly.
                ArithOp::Add => lhs.checked_add(rhs),
                ArithOp::Mul => lhs.checked_mul(rhs),
                ArithOp::Sub => Some(lhs.saturating_sub(rhs)),
                ArithOp::Div => Some(lhs / rhs),
                ArithOp::Rem => Some(lhs % rhs),
                ArithOp::BitAnd => Some(lhs & rhs),
                ArithOp::BitOr => Some(lhs | rhs),
                ArithOp::BitXor => Some(lhs ^ rhs),
            }
            .ok_or_else(|| {
                "Nat monitor evaluation exceeded the exact u128 test representation".into()
            }),
            Some(bits) => {
                if bits < 1 || bits > 128 {
                    return Err(format!(
                        "`{}` has BitVec width {bits}; the width helpers accept 1..=128",
                        self.source_name()
                    ));
                }
                let mask = bit_mask(bits);
                // Only `+`/`-`/`*` can overflow the width and need masking.
                // `/`/`%` and the bitwise ops of in-range operands are already
                // in range.
                match op {
                    // The zero-divisor check sits in this match for the reason
                    // given on the `Nat` arm above.
                    ArithOp::Div | ArithOp::Rem if rhs == 0 => {
                        return Err("monitor runtime: division or remainder by zero".into());
                    }
                    ArithOp::Add => Ok(lhs.wrapping_add(rhs) & mask),
                    ArithOp::Sub => Ok(lhs.wrapping_sub(rhs) & mask),
                    ArithOp::Mul => Ok(lhs.wrapping_mul(rhs) & mask),
                    ArithOp::Div => Ok(lhs / rhs),
                    ArithOp::Rem => Ok(lhs % rhs),
                    ArithOp::BitAnd => Ok(lhs & rhs),
                    ArithOp::BitOr => Ok(lhs | rhs),
                    ArithOp::BitXor => Ok(lhs ^ rhs),
                }
            }
        }
    }

    fn signed_value(self, value: u128) -> Result<i128, String> {
        let Some(bits) = self.bits().filter(|_| self.is_signed()) else {
            return Err(format!("`{}` is not a signed runtime carrier", self.source_name()));
        };
        if bits < 1 || bits > 128 {
            return Err(format!(
                "`{}` has BitVec width {bits}; the width helpers accept 1..=128",
                self.source_name()
            ));
        }
        let value = self.normalize(value)?;
        if bits == 128 {
            Ok(value as i128)
        } else {
            let sign = 1u128 << (bits - 1);
            let extended = if value & sign == 0 { value } else { value | !bit_mask(bits) };
            Ok(extended as i128)
        }
    }

    fn compare(self, lhs: u128, rhs: u128, op: CompareOp) -> Result<bool, String> {
        if self == Self::Bool {
            return Err("boolean monitor values are not ordered".into());
        }
        if self.is_signed() {
            let (lhs, rhs) = (self.signed_value(lhs)?, self.signed_value(rhs)?);
            return Ok(match op {
                CompareOp::Le => lhs <= rhs,
                CompareOp::Lt => lhs < rhs,
                CompareOp::Ge => lhs >= rhs,
                CompareOp::Gt => lhs > rhs,
            });
        }
        Ok(match op {
            CompareOp::Le => lhs <= rhs,
            CompareOp::Lt => lhs < rhs,
            CompareOp::Ge => lhs >= rhs,
            CompareOp::Gt => lhs > rhs,
        })
    }
}

/// The arithmetic operation a [`RuntimeMonitorExpr`] term applies, selecting
/// the domain's exact/truncated/wrapping semantics in [`RuntimeMonitorDomain::wrapping_bin`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ArithOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    BitAnd,
    BitOr,
    BitXor,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CompareOp {
    Le,
    Lt,
    Ge,
    Gt,
}

/// Fully bound executable payload carried by a [`CertifiedMonitor`]. Its
/// fields are private so executable trees can only be minted by the certified
/// construction path in this crate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RuntimeMonitor {
    variables: Vec<String>,
    /// The runtime carrier of EACH variable. In a single-domain clause every
    /// entry is the same; a mixed clause (`flag && x < 10`) carries a `Bool` and
    /// a `UInt64`. Each argument is normalized by its own carrier.
    domains: BTreeMap<String, RuntimeMonitorDomain>,
    expr: RuntimeMonitorExpr,
}

impl RuntimeMonitor {
    /// Variables in first source-occurrence order.
    #[must_use]
    pub fn variables(&self) -> &[String] {
        &self.variables
    }

    /// Exact runtime carrier of every variable.
    #[must_use]
    pub fn domains(&self) -> &BTreeMap<String, RuntimeMonitorDomain> {
        &self.domains
    }

    /// Certified executable syntax tree.
    #[must_use]
    pub fn expr(&self) -> &RuntimeMonitorExpr {
        &self.expr
    }

    /// Runtime carrier of one certified variable.
    #[must_use]
    pub fn domain(&self, name: &str) -> Option<RuntimeMonitorDomain> {
        self.domains.get(name).copied()
    }

    fn collect_term_domain(
        &self,
        expr: &RuntimeMonitorExpr,
        domain: &mut Option<RuntimeMonitorDomain>,
    ) -> Result<(), String> {
        match expr {
            RuntimeMonitorExpr::Var(name) => {
                let found = self
                    .domain(name)
                    .ok_or_else(|| format!("certified monitor has no domain for `{name}`"))?;
                match domain {
                    None => *domain = Some(found),
                    Some(expected) if *expected == found => {}
                    Some(expected) => {
                        return Err(format!(
                            "monitor atom mixes runtime domains {expected:?} and {found:?}"
                        ));
                    }
                }
                Ok(())
            }
            RuntimeMonitorExpr::Zero | RuntimeMonitorExpr::Lit(_) => Ok(()),
            RuntimeMonitorExpr::Add(lhs, rhs)
            | RuntimeMonitorExpr::Sub(lhs, rhs)
            | RuntimeMonitorExpr::Mul(lhs, rhs)
            | RuntimeMonitorExpr::Div(lhs, rhs)
            | RuntimeMonitorExpr::Rem(lhs, rhs)
            | RuntimeMonitorExpr::BitAnd(lhs, rhs)
            | RuntimeMonitorExpr::BitOr(lhs, rhs)
            | RuntimeMonitorExpr::BitXor(lhs, rhs) => {
                self.collect_term_domain(lhs, domain)?;
                self.collect_term_domain(rhs, domain)
            }
            _ => Err("monitor proposition used where a term domain was required".into()),
        }
    }

    fn term_domain(
        &self,
        lhs: &RuntimeMonitorExpr,
        rhs: &RuntimeMonitorExpr,
    ) -> Result<RuntimeMonitorDomain, String> {
        let mut domain = None;
        self.collect_term_domain(lhs, &mut domain)?;
        self.collect_term_domain(rhs, &mut domain)?;
        Ok(domain.unwrap_or(RuntimeMonitorDomain::Nat))
    }

    /// Exact reference evaluator used by wiring tests and non-codegen
    /// consumers. Missing, duplicate, or extra arguments are errors: runtime
    /// monitoring never invents a value or ignores a binding.
    pub fn evaluate(&self, args: &[(&str, u128)]) -> Result<bool, String> {
        if args.len() != self.variables.len() {
            return Err(format!(
                "monitor expected {} argument(s), got {}",
                self.variables.len(),
                args.len()
            ));
        }
        let mut values = std::collections::BTreeMap::new();
        for (name, value) in args {
            let carrier = self
                .domains
                .get(*name)
                .ok_or_else(|| format!("unexpected monitor argument `{name}`"))?;
            if values.insert(*name, carrier.normalize(*value)?).is_some() {
                return Err(format!("duplicate monitor argument `{name}`"));
            }
        }
        for name in &self.variables {
            if !values.contains_key(name.as_str()) {
                return Err(format!("missing monitor argument `{name}`"));
            }
        }
        if let Some(extra) =
            values.keys().find(|name| !self.variables.iter().any(|v| v.as_str() == **name))
        {
            return Err(format!("unexpected monitor argument `{extra}`"));
        }
        self.eval_prop(&self.expr, &values)
    }

    fn eval_term(
        &self,
        expr: &RuntimeMonitorExpr,
        values: &std::collections::BTreeMap<&str, u128>,
        domain: RuntimeMonitorDomain,
    ) -> Result<u128, String> {
        eval_term_with_domains(&self.domains, expr, values, domain)
    }

    fn eval_prop(
        &self,
        expr: &RuntimeMonitorExpr,
        values: &std::collections::BTreeMap<&str, u128>,
    ) -> Result<bool, String> {
        let terms = |lhs: &RuntimeMonitorExpr, rhs: &RuntimeMonitorExpr| {
            let domain = self.term_domain(lhs, rhs)?;
            Ok::<_, String>((
                domain,
                self.eval_term(lhs, values, domain)?,
                self.eval_term(rhs, values, domain)?,
            ))
        };
        match expr {
            RuntimeMonitorExpr::Eq(lhs, rhs) => {
                let (_, lhs, rhs) = terms(lhs, rhs)?;
                Ok(lhs == rhs)
            }
            RuntimeMonitorExpr::Le(lhs, rhs) => {
                let (domain, lhs, rhs) = terms(lhs, rhs)?;
                domain.compare(lhs, rhs, CompareOp::Le)
            }
            RuntimeMonitorExpr::Lt(lhs, rhs) => {
                let (domain, lhs, rhs) = terms(lhs, rhs)?;
                domain.compare(lhs, rhs, CompareOp::Lt)
            }
            RuntimeMonitorExpr::Ge(lhs, rhs) => {
                let (domain, lhs, rhs) = terms(lhs, rhs)?;
                domain.compare(lhs, rhs, CompareOp::Ge)
            }
            RuntimeMonitorExpr::Gt(lhs, rhs) => {
                let (domain, lhs, rhs) = terms(lhs, rhs)?;
                domain.compare(lhs, rhs, CompareOp::Gt)
            }
            RuntimeMonitorExpr::And(lhs, rhs) => {
                Ok(self.eval_prop(lhs, values)? && self.eval_prop(rhs, values)?)
            }
            RuntimeMonitorExpr::Or(lhs, rhs) => {
                Ok(self.eval_prop(lhs, values)? || self.eval_prop(rhs, values)?)
            }
            RuntimeMonitorExpr::Not(inner) => Ok(!self.eval_prop(inner, values)?),
            _ => Err("term used where a monitor proposition was required".into()),
        }
    }
}

fn eval_term_with_domains(
    domains: &BTreeMap<String, RuntimeMonitorDomain>,
    expr: &RuntimeMonitorExpr,
    values: &std::collections::BTreeMap<&str, u128>,
    domain: RuntimeMonitorDomain,
) -> Result<u128, String> {
    match expr {
        RuntimeMonitorExpr::Var(name) => {
            let actual = domains
                .get(name.as_str())
                .copied()
                .ok_or_else(|| format!("certified monitor has no domain for `{name}`"))?;
            if actual != domain {
                return Err(format!(
                    "monitor term uses `{name}` as {domain:?}, but it is bound as {actual:?}"
                ));
            }
            values
                .get(name.as_str())
                .copied()
                .ok_or_else(|| format!("missing monitor argument `{name}`"))
        }
        RuntimeMonitorExpr::Zero => Ok(0),
        RuntimeMonitorExpr::Lit(v) => domain.normalize(*v),
        RuntimeMonitorExpr::Add(lhs, rhs) => domain.wrapping_bin(
            eval_term_with_domains(domains, lhs, values, domain)?,
            eval_term_with_domains(domains, rhs, values, domain)?,
            ArithOp::Add,
        ),
        RuntimeMonitorExpr::Sub(lhs, rhs) => domain.wrapping_bin(
            eval_term_with_domains(domains, lhs, values, domain)?,
            eval_term_with_domains(domains, rhs, values, domain)?,
            ArithOp::Sub,
        ),
        RuntimeMonitorExpr::Mul(lhs, rhs) => domain.wrapping_bin(
            eval_term_with_domains(domains, lhs, values, domain)?,
            eval_term_with_domains(domains, rhs, values, domain)?,
            ArithOp::Mul,
        ),
        RuntimeMonitorExpr::Div(lhs, rhs) => domain.wrapping_bin(
            eval_term_with_domains(domains, lhs, values, domain)?,
            eval_term_with_domains(domains, rhs, values, domain)?,
            ArithOp::Div,
        ),
        RuntimeMonitorExpr::Rem(lhs, rhs) => domain.wrapping_bin(
            eval_term_with_domains(domains, lhs, values, domain)?,
            eval_term_with_domains(domains, rhs, values, domain)?,
            ArithOp::Rem,
        ),
        RuntimeMonitorExpr::BitAnd(lhs, rhs) => domain.wrapping_bin(
            eval_term_with_domains(domains, lhs, values, domain)?,
            eval_term_with_domains(domains, rhs, values, domain)?,
            ArithOp::BitAnd,
        ),
        RuntimeMonitorExpr::BitOr(lhs, rhs) => domain.wrapping_bin(
            eval_term_with_domains(domains, lhs, values, domain)?,
            eval_term_with_domains(domains, rhs, values, domain)?,
            ArithOp::BitOr,
        ),
        RuntimeMonitorExpr::BitXor(lhs, rhs) => domain.wrapping_bin(
            eval_term_with_domains(domains, lhs, values, domain)?,
            eval_term_with_domains(domains, rhs, values, domain)?,
            ArithOp::BitXor,
        ),
        _ => Err("proposition used where a monitor term was required".into()),
    }
}

/// A certified runtime monitor for a clause (two-language design §1.1): a
/// Bool decision procedure `monitor(vars) : Bool` together with the required
/// KERNEL-CHECKED equivalence certificate
/// `∀ vars, (monitor vars = true) ↔ P`.
///
/// The executable shape and the Clean term are derived from the same parsed
/// expression. A runtime lane may execute the payload only because
/// `equivalence_proof` passed the strict rooted certification audit: only the
/// canonical foundations are allowed and trust markers are rejected. The
/// `monitor = true → P` direction is the one-direction
/// soundness certificate (passing the check entails the clause); the added
/// completeness direction `P → monitor = true` is what makes runtime
/// execution non-aborting on satisfied clauses, so it is REQUIRED for an
/// executable monitor, not decorative.
///
/// The carrier is deliberately sealed: external callers can inspect the
/// checked terms and extract the executable payload, but cannot construct a
/// `CertifiedMonitor` from arbitrary expressions. A standalone
/// [`RuntimeMonitor`] remains only data; it does not inherit this provenance.
#[derive(Debug, Clone)]
pub struct CertifiedMonitor {
    /// The Bool decision term `λ vars. <decide>` over the clause variables.
    monitor: Expr,
    /// The corresponding executable expression; never present without the
    /// equivalence certificate.
    runtime: RuntimeMonitor,
    /// The theorem statement `∀ vars, (monitor vars = true) ↔ P`.
    equivalence_goal: Expr,
    /// The proof term inhabiting `equivalence_goal` (kernel-checked).
    equivalence_proof: Expr,
}

impl CertifiedMonitor {
    /// The certified Boolean monitor term. Reading this term grants no Rust VC
    /// or check-elision authority.
    #[must_use]
    pub fn monitor(&self) -> &Expr {
        &self.monitor
    }

    /// The executable monitor payload (borrowed).
    #[must_use]
    pub fn runtime(&self) -> &RuntimeMonitor {
        &self.runtime
    }

    /// Consume this certificate carrier, keeping only its executable payload.
    /// The returned raw payload carries no independently checkable provenance;
    /// consumers needing certification authority must retain this sealed
    /// carrier or a compiler-private binding derived from it.
    #[must_use]
    pub fn into_runtime(self) -> RuntimeMonitor {
        self.runtime
    }

    /// The exact equivalence theorem checked by the Clean kernel.
    #[must_use]
    pub fn equivalence_goal(&self) -> &Expr {
        &self.equivalence_goal
    }

    /// The proof term inhabiting [`Self::equivalence_goal`].
    #[must_use]
    pub fn equivalence_proof(&self) -> &Expr {
        &self.equivalence_proof
    }
}

/// Executable scalar term paired with a [`CertifiedScalarTerm`].
///
/// This raw payload is inspectable and clonable, but only the sealed certified
/// carrier proves that it came from the same typed syntax as a kernel-checked
/// Clean term. Values use the exact runtime bit pattern for fixed-width
/// carriers; signed results are therefore returned in two's-complement form.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RuntimeScalarTerm {
    variables: Vec<String>,
    domains: BTreeMap<String, RuntimeMonitorDomain>,
    domain: RuntimeMonitorDomain,
    expr: RuntimeMonitorExpr,
}

impl RuntimeScalarTerm {
    /// Variables in first source-occurrence order.
    #[must_use]
    pub fn variables(&self) -> &[String] {
        &self.variables
    }

    /// Exact runtime carrier of each variable.
    #[must_use]
    pub fn domains(&self) -> &BTreeMap<String, RuntimeMonitorDomain> {
        &self.domains
    }

    /// The scalar result carrier.
    #[must_use]
    pub const fn domain(&self) -> RuntimeMonitorDomain {
        self.domain
    }

    /// Certified executable syntax tree.
    #[must_use]
    pub fn expr(&self) -> &RuntimeMonitorExpr {
        &self.expr
    }

    /// Evaluate the term exactly in its Nat or wrapping bitvector domain.
    pub fn evaluate(&self, args: &[(&str, u128)]) -> Result<u128, String> {
        if args.len() != self.variables.len() {
            return Err(format!(
                "scalar term expected {} argument(s), got {}",
                self.variables.len(),
                args.len()
            ));
        }
        let mut values = BTreeMap::new();
        for (name, value) in args {
            let carrier = self
                .domains
                .get(*name)
                .ok_or_else(|| format!("unexpected scalar-term argument `{name}`"))?;
            if values.insert(*name, carrier.normalize(*value)?).is_some() {
                return Err(format!("duplicate scalar-term argument `{name}`"));
            }
        }
        for name in &self.variables {
            if !values.contains_key(name.as_str()) {
                return Err(format!("missing scalar-term argument `{name}`"));
            }
        }
        eval_term_with_domains(&self.domains, &self.expr, &values, self.domain)
    }
}

/// A sealed scalar/measure evaluator whose Clean term and typed source
/// projection were tied by a kernel-checked equality theorem.
///
/// The binding theorem is proved by reflexivity only after two independent
/// projections — source AST elaboration and executable-tree reconstruction —
/// reduce to the same kernel term. Kernel checking therefore checks both the
/// exact Nat/BitVec carrier under every typed binder and definitional agreement
/// of the runtime representation with the source semantics. External code
/// cannot forge this carrier.
#[derive(Debug, Clone)]
pub struct CertifiedScalarTerm {
    kernel_term: Expr,
    runtime: RuntimeScalarTerm,
    domain: Domain,
    binding_goal: Expr,
    binding_proof: Expr,
}

impl CertifiedScalarTerm {
    /// The closed Clean function `λ vars. term`.
    #[must_use]
    pub fn kernel_term(&self) -> &Expr {
        &self.kernel_term
    }

    /// Exact executable scalar evaluator.
    #[must_use]
    pub fn runtime(&self) -> &RuntimeScalarTerm {
        &self.runtime
    }

    /// The exact elaboration domain.
    #[must_use]
    pub fn domain(&self) -> &Domain {
        &self.domain
    }

    /// Kernel-checked equality tying the closed term to its typed projection.
    #[must_use]
    pub fn binding_goal(&self) -> &Expr {
        &self.binding_goal
    }

    /// Proof term inhabiting [`Self::binding_goal`].
    #[must_use]
    pub fn binding_proof(&self) -> &Expr {
        &self.binding_proof
    }

    /// Consume the certificate carrier, retaining only the raw evaluator.
    #[must_use]
    pub fn into_runtime(self) -> RuntimeScalarTerm {
        self.runtime
    }
}

/// E5-facing name for a certified scalar term.
pub type CertifiedMeasure = CertifiedScalarTerm;

fn runtime_monitor_term(
    ast: &SynExpr,
    domain: &Domain,
    var_domains: &BTreeMap<String, Domain>,
) -> Result<RuntimeMonitorExpr, String> {
    match ast {
        SynExpr::Paren(p) => runtime_monitor_term(&p.expr, domain, var_domains),
        SynExpr::Path(p) => {
            let id = p
                .path
                .get_ident()
                .ok_or_else(|| "monitor runtime: only bare identifiers are supported".to_string())?
                .to_string();
            let actual = var_domains
                .get(&id)
                .ok_or_else(|| format!("monitor runtime: unbound variable `{id}`"))?;
            if actual != domain {
                return Err(format!(
                    "monitor runtime: `{id}` has domain {actual:?}, expected {domain:?}"
                ));
            }
            Ok(RuntimeMonitorExpr::Var(id))
        }
        SynExpr::Lit(l) => match &l.lit {
            Lit::Int(i) => {
                let n: u128 = i
                    .base10_parse()
                    .map_err(|e| format!("monitor runtime: bad int literal: {e}"))?;
                if domain.is_bool() {
                    return Err("monitor runtime: an integer literal is not a `bool`".into());
                }
                let _ = domain.numeral(n)?;
                if n == 0 { Ok(RuntimeMonitorExpr::Zero) } else { Ok(RuntimeMonitorExpr::Lit(n)) }
            }
            Lit::Bool(b) if domain.is_bool() => Ok(RuntimeMonitorExpr::Lit(u128::from(b.value))),
            Lit::Bool(_) => {
                Err("monitor runtime: a bool literal requires the `bool` carrier".into())
            }
            _ => Err("monitor runtime: unsupported literal".into()),
        },
        SynExpr::Unary(u) if matches!(u.op, syn::UnOp::Neg(_)) => {
            if !domain.is_signed() {
                return Err(format!(
                    "monitor runtime: unary negation requires a signed carrier, not `{}`",
                    domain.rust_name()
                ));
            }
            if let Some(magnitude) = nonneg_int_literal(&u.expr) {
                let _ = domain.negative_numeral(magnitude)?;
                let Some(bits) = domain.bitvec_bits() else {
                    return Err(format!(
                        "monitor runtime: unary negation requires a signed carrier, not `{}`",
                        domain.rust_name()
                    ));
                };
                if bits < 1 || bits > 128 {
                    return Err(format!(
                        "`{}` has BitVec width {bits}; the width helpers accept 1..=128",
                        domain.rust_name()
                    ));
                }
                let pattern = 0u128.wrapping_sub(magnitude) & bit_mask(bits);
                return Ok(if pattern == 0 {
                    RuntimeMonitorExpr::Zero
                } else {
                    RuntimeMonitorExpr::Lit(pattern)
                });
            }
            Ok(RuntimeMonitorExpr::Sub(
                Box::new(RuntimeMonitorExpr::Zero),
                Box::new(runtime_monitor_term(&u.expr, domain, var_domains)?),
            ))
        }
        SynExpr::Binary(b) => {
            if domain.is_bool() {
                return Err("monitor runtime: arithmetic is not supported for `bool`".into());
            }
            if domain.is_signed() && matches!(b.op, BinOp::Div(_) | BinOp::Rem(_)) {
                return Err(format!(
                    "monitor runtime: signed division/remainder is not implemented for `{}`",
                    domain.rust_name()
                ));
            }
            if domain.is_signed() && matches!(b.op, BinOp::Shr(_)) {
                return Err(format!(
                    "monitor runtime: signed right shift is not implemented for `{}`",
                    domain.rust_name()
                ));
            }
            let lhs = Box::new(runtime_monitor_term(&b.left, domain, var_domains)?);
            let rhs = Box::new(runtime_monitor_term(&b.right, domain, var_domains)?);
            Ok(match b.op {
                BinOp::Add(_) => RuntimeMonitorExpr::Add(lhs, rhs),
                BinOp::Sub(_) => RuntimeMonitorExpr::Sub(lhs, rhs),
                BinOp::Mul(_) => RuntimeMonitorExpr::Mul(lhs, rhs),
                BinOp::BitAnd(_) => RuntimeMonitorExpr::BitAnd(lhs, rhs),
                BinOp::BitOr(_) => RuntimeMonitorExpr::BitOr(lhs, rhs),
                BinOp::BitXor(_) => RuntimeMonitorExpr::BitXor(lhs, rhs),
                // `x << n` / `x >> n` decide as `x * 2^n` / `x / 2^n` — the same
                // reduction the kernel side uses.
                BinOp::Shl(_) | BinOp::Shr(_) => {
                    let Some(n) = nonneg_int_literal(&b.right) else {
                        return Err(
                            "monitor runtime: bit-shift requires a literal shift amount".into()
                        );
                    };
                    let finite_bits = match domain {
                        Domain::Machine(width) => Some(width.bits()),
                        _ => domain.bitvec_bits(),
                    };
                    if let Some(bits) = finite_bits {
                        if n >= u128::from(bits) {
                            return Err(format!(
                                "monitor runtime: shift amount {n} is out of range for `{}`",
                                domain.rust_name()
                            ));
                        }
                    }
                    // Keep the executable twin in the same `< 128` fragment as
                    // kernel elaboration. A lossy `as u32` here would turn, for
                    // example, 2^32 into a shift by zero.
                    let shift = u32::try_from(n)
                        .map_err(|_| "monitor runtime: shift amount too large (>= 128)")?;
                    let two_pow_n = 1u128
                        .checked_shl(shift)
                        .ok_or("monitor runtime: shift amount too large (>= 128)")?;
                    let pow = Box::new(RuntimeMonitorExpr::Lit(two_pow_n));
                    if matches!(b.op, BinOp::Shl(_)) {
                        RuntimeMonitorExpr::Mul(lhs, pow)
                    } else {
                        RuntimeMonitorExpr::Div(lhs, pow)
                    }
                }
                // `/`/`%` mirror the kernel-side gate: a positive-literal
                // divisor only, so the runtime never divides by zero.
                BinOp::Div(_) | BinOp::Rem(_) => {
                    if positive_int_literal(&b.right).is_none() {
                        return Err("monitor runtime: division/remainder requires a positive \
                                    integer literal divisor"
                            .into());
                    }
                    if matches!(b.op, BinOp::Div(_)) {
                        RuntimeMonitorExpr::Div(lhs, rhs)
                    } else {
                        RuntimeMonitorExpr::Rem(lhs, rhs)
                    }
                }
                _ => return Err("monitor runtime: unsupported binary operator".into()),
            })
        }
        _ => Err("monitor runtime: unsupported expression shape".into()),
    }
}

/// Reconstruct the Clean scalar term denoted by an executable tree.
///
/// This is intentionally independent of [`elab_term`]: the scalar certificate
/// proves this runtime-side reconstruction definitionally equal to the
/// source-side elaboration. A future change that drifts either projection
/// therefore makes the kernel reject the binding theorem.
fn runtime_scalar_clean_term(
    expr: &RuntimeMonitorExpr,
    vars: &[String],
    offset: u32,
    domain: &Domain,
    var_domains: &BTreeMap<String, Domain>,
) -> Result<Expr, String> {
    let recurse = |expr| runtime_scalar_clean_term(expr, vars, offset, domain, var_domains);
    match expr {
        RuntimeMonitorExpr::Var(name) => {
            let actual =
                var_domains.get(name).ok_or_else(|| format!("unbound variable `{name}`"))?;
            if actual != domain {
                return Err(format!(
                    "runtime scalar `{name}` has domain {actual:?}, expected {domain:?}"
                ));
            }
            let pos = vars
                .iter()
                .position(|var| var == name)
                .ok_or_else(|| format!("unbound variable `{name}`"))?;
            Ok(Expr::bvar(de_bruijn_index(vars.len(), pos, offset)?))
        }
        RuntimeMonitorExpr::Zero => Ok(domain.zero()),
        RuntimeMonitorExpr::Lit(value) => match domain {
            Domain::RegisteredAdt(_) => Err(domain.registered_operation_refusal("runtime monitoring")),
            Domain::Int => Err("`int` is a kernel-goal-only domain (the nat-lift codomain): it has no executable runtime carrier, so a clause that reaches it is `unmonitored` rather than monitored at a guessed width".into()),
            Domain::Nat | Domain::Machine(_) => domain.numeral(*value),
            Domain::Signed(_) | Domain::U128 | Domain::USize(_) | Domain::ISize(_) => {
                domain.runtime_domain()?.normalize(*value)?;
                domain.bitvec_of_nat(kernel_nat_lit(*value))
            }
            Domain::Bool => Err("a scalar term cannot use a bool literal".into()),
            Domain::OptionSigned(_) => {
                Err("a scalar term cannot inhabit an Option carrier".into())
            }
        },
        RuntimeMonitorExpr::Add(lhs, rhs) => domain.arithmetic("add", recurse(lhs)?, recurse(rhs)?),
        RuntimeMonitorExpr::Sub(lhs, rhs) => domain.arithmetic("sub", recurse(lhs)?, recurse(rhs)?),
        RuntimeMonitorExpr::Mul(lhs, rhs) => domain.arithmetic("mul", recurse(lhs)?, recurse(rhs)?),
        RuntimeMonitorExpr::Div(lhs, rhs) | RuntimeMonitorExpr::Rem(lhs, rhs) => {
            if domain.is_signed() {
                return Err("signed division/remainder is not implemented".into());
            }
            let op =
                if matches!(expr, RuntimeMonitorExpr::Div(_, _)) { "Nat.div" } else { "Nat.mod" };
            let lhs = recurse(lhs)?;
            let rhs = recurse(rhs)?;
            let nat_bin =
                |lhs, rhs| Expr::apps(Expr::const_(Name::interned(op), vec![]), [lhs, rhs]);
            match domain {
                Domain::Nat => Ok(nat_bin(lhs, rhs)),
                Domain::Machine(width) => {
                    let to_nat = Expr::const_(Name::interned(width.to_nat_const()), vec![]);
                    let lhs = Expr::app(to_nat.clone(), lhs);
                    let rhs = Expr::app(to_nat, rhs);
                    Ok(Expr::app(
                        Expr::const_(Name::interned(width.of_nat_const()), vec![]),
                        nat_bin(lhs, rhs),
                    ))
                }
                Domain::U128 | Domain::USize(_) => {
                    let lhs = domain.bitvec_to_nat(lhs)?;
                    let rhs = domain.bitvec_to_nat(rhs)?;
                    domain.bitvec_of_nat(nat_bin(lhs, rhs))
                }
                Domain::Int
                | Domain::Signed(_)
                | Domain::ISize(_)
                | Domain::Bool
                | Domain::RegisteredAdt(_)
                | Domain::OptionSigned(_) => {
                    Err("division/remainder is unsupported for this scalar domain".into())
                }
            }
        }
        RuntimeMonitorExpr::BitAnd(lhs, rhs)
        | RuntimeMonitorExpr::BitOr(lhs, rhs)
        | RuntimeMonitorExpr::BitXor(lhs, rhs) => {
            let op = match expr {
                RuntimeMonitorExpr::BitAnd(_, _) => "Nat.land",
                RuntimeMonitorExpr::BitOr(_, _) => "Nat.lor",
                _ => "Nat.xor",
            };
            let lhs = recurse(lhs)?;
            let rhs = recurse(rhs)?;
            let nat_bin =
                |lhs, rhs| Expr::apps(Expr::const_(Name::interned(op), vec![]), [lhs, rhs]);
            match domain {
                Domain::Nat => Ok(nat_bin(lhs, rhs)),
                Domain::Machine(width) => {
                    let to_nat = Expr::const_(Name::interned(width.to_nat_const()), vec![]);
                    let lhs = Expr::app(to_nat.clone(), lhs);
                    let rhs = Expr::app(to_nat, rhs);
                    Ok(Expr::app(
                        Expr::const_(Name::interned(width.of_nat_const()), vec![]),
                        nat_bin(lhs, rhs),
                    ))
                }
                Domain::Signed(_) | Domain::U128 | Domain::USize(_) | Domain::ISize(_) => {
                    let lhs = domain.bitvec_to_nat(lhs)?;
                    let rhs = domain.bitvec_to_nat(rhs)?;
                    domain.bitvec_of_nat(nat_bin(lhs, rhs))
                }
                Domain::Bool => Err("bitwise operations are unsupported for bool".into()),
                Domain::RegisteredAdt(_) => Err(domain.registered_operation_refusal("runtime monitoring")),
                Domain::Int => Err("`int` is a kernel-goal-only domain (the nat-lift codomain): it has no executable runtime carrier, so a clause that reaches it is `unmonitored` rather than monitored at a guessed width".into()),
                Domain::OptionSigned(_) => {
                    Err("bitwise operations are unsupported for an Option carrier".into())
                }
            }
        }
        RuntimeMonitorExpr::Eq(_, _)
        | RuntimeMonitorExpr::Le(_, _)
        | RuntimeMonitorExpr::Lt(_, _)
        | RuntimeMonitorExpr::Ge(_, _)
        | RuntimeMonitorExpr::Gt(_, _)
        | RuntimeMonitorExpr::And(_, _)
        | RuntimeMonitorExpr::Or(_, _)
        | RuntimeMonitorExpr::Not(_) => {
            Err("a proposition appeared in a scalar runtime term".into())
        }
    }
}

/// Project the parsed clause into the executable tree with proposition/term
/// context and the exact domain of each atom. Connectives may combine atoms of
/// different carriers; arithmetic inherits only its enclosing atom's carrier.
fn runtime_monitor_prop(
    ast: &SynExpr,
    var_domains: &BTreeMap<String, Domain>,
) -> Result<RuntimeMonitorExpr, String> {
    match ast {
        SynExpr::Paren(p) => runtime_monitor_prop(&p.expr, var_domains),
        SynExpr::Unary(u) if matches!(u.op, syn::UnOp::Not(_)) => {
            Ok(RuntimeMonitorExpr::Not(Box::new(runtime_monitor_prop(&u.expr, var_domains)?)))
        }
        SynExpr::Binary(b) if matches!(b.op, BinOp::And(_)) => Ok(RuntimeMonitorExpr::And(
            Box::new(runtime_monitor_prop(&b.left, var_domains)?),
            Box::new(runtime_monitor_prop(&b.right, var_domains)?),
        )),
        SynExpr::Binary(b) if matches!(b.op, BinOp::Or(_)) => Ok(RuntimeMonitorExpr::Or(
            Box::new(runtime_monitor_prop(&b.left, var_domains)?),
            Box::new(runtime_monitor_prop(&b.right, var_domains)?),
        )),
        SynExpr::Binary(b) if matches!(b.op, BinOp::Ne(_)) => {
            runtime_monitor_prop(&ne_as_not_eq(b), var_domains)
        }
        SynExpr::Path(p) => {
            let id = p
                .path
                .get_ident()
                .ok_or_else(|| "monitor runtime: only bare identifiers are supported".to_string())?
                .to_string();
            if !var_domains.get(&id).is_some_and(Domain::is_bool) {
                return Err("monitor runtime: a bare identifier proposition requires `bool`".into());
            }
            Ok(RuntimeMonitorExpr::Eq(
                Box::new(RuntimeMonitorExpr::Var(id)),
                Box::new(RuntimeMonitorExpr::Lit(1)),
            ))
        }
        SynExpr::Lit(l) if matches!(&l.lit, Lit::Bool(_)) => {
            let value = matches!(&l.lit, Lit::Bool(b) if b.value);
            Ok(RuntimeMonitorExpr::Eq(
                Box::new(RuntimeMonitorExpr::Lit(u128::from(value))),
                Box::new(RuntimeMonitorExpr::Lit(1)),
            ))
        }
        SynExpr::Binary(b)
            if matches!(
                b.op,
                BinOp::Eq(_) | BinOp::Le(_) | BinOp::Lt(_) | BinOp::Ge(_) | BinOp::Gt(_)
            ) =>
        {
            let domain = atom_domain(ast, var_domains)?;
            if domain.is_bool()
                && matches!(b.op, BinOp::Le(_) | BinOp::Lt(_) | BinOp::Ge(_) | BinOp::Gt(_))
            {
                return Err("monitor runtime: `bool` values are not ordered".into());
            }
            let lhs = Box::new(runtime_monitor_term(&b.left, &domain, var_domains)?);
            let rhs = Box::new(runtime_monitor_term(&b.right, &domain, var_domains)?);
            Ok(match b.op {
                BinOp::Eq(_) => RuntimeMonitorExpr::Eq(lhs, rhs),
                BinOp::Le(_) => RuntimeMonitorExpr::Le(lhs, rhs),
                BinOp::Lt(_) => RuntimeMonitorExpr::Lt(lhs, rhs),
                BinOp::Ge(_) => RuntimeMonitorExpr::Ge(lhs, rhs),
                BinOp::Gt(_) => RuntimeMonitorExpr::Gt(lhs, rhs),
                _ => return Err("monitor runtime: unsupported proposition shape".into()),
            })
        }
        _ => Err("monitor runtime: unsupported proposition shape".into()),
    }
}

/// How a comparison decides through `Nat.ble` + the `Nat.le_of_ble_eq_true`
/// certificate. `Nat.lt a b` is DEFINITIONALLY `Nat.le (Nat.succ a) b`, so all
/// four comparisons route through the single `ble`/`le` bridge lemma:
///   `a <= b` → `ble a b`;          `a < b` → `ble (succ a) b`;
///   `a >= b` → `ble b a`  (swap);  `a > b` → `ble (succ b) a` (swap + succ).
/// Returns `(swap_operands, succ_on_smaller_side)`.
fn comparison_decision(op: &BinOp) -> Option<(bool, bool)> {
    match op {
        BinOp::Le(_) => Some((false, false)),
        BinOp::Lt(_) => Some((false, true)),
        BinOp::Ge(_) => Some((true, false)),
        BinOp::Gt(_) => Some((true, true)),
        _ => None,
    }
}

/// `Nat.succ e`.
fn nat_succ(e: Expr) -> Expr {
    Expr::app(Expr::const_(Name::interned("Nat.succ"), vec![]), e)
}

/// `Eq.{1} Bool x <lit>` — the `x = true`/`x = false` proposition for a Bool
/// decision (`lit` = `Bool.true` / `Bool.false`).
fn bool_eq_expr(lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::interned("Eq"), vec![Level::succ(Level::zero())]),
        [Expr::const_(Name::interned("Bool"), vec![]), lhs, rhs],
    )
}

fn bool_eq(x: Expr, lit: &str) -> Expr {
    bool_eq_expr(x, Expr::const_(Name::interned(lit), vec![]))
}

/// `x = true`.
fn bool_eq_true(x: Expr) -> Expr {
    bool_eq(x, "Bool.true")
}

/// `x = false`.
fn bool_eq_false(x: Expr) -> Expr {
    bool_eq(x, "Bool.false")
}

/// `Not p` (`p → False`).
fn not_prop(p: Expr) -> Expr {
    Expr::app(Expr::const_(Name::interned("Not"), vec![]), p)
}

/// The `(small, large)` Nat operands of a comparison's `Nat.ble` at binder
/// `offset`: machine ints go through `<Carrier>.toNat` (the carrier's order IS
/// `toNat` order); `>=`/`>` swap the operands; the smaller side gets `succ` for
/// strict `<`/`>` (`Nat.lt a b ≡ Nat.le (succ a) b`). Shared by the positive
/// comparison monitor and the negation lane.
fn ble_operands_with_domains(
    b: &syn::ExprBinary,
    vars: &[String],
    offset: u32,
    var_domains: &BTreeMap<String, Domain>,
    dom: &Domain,
) -> Result<(Expr, Expr), String> {
    let (swap, strict) = comparison_decision(&b.op)
        .ok_or_else(|| "monitor fragment: only <= < >= > are supported".to_string())?;
    let to_nat = |e: Expr| -> Result<Expr, String> {
        Ok(match dom {
            Domain::Nat => e,
            Domain::Machine(width) => {
                Expr::app(Expr::const_(Name::interned(width.to_nat_const()), vec![]), e)
            }
            Domain::Signed(_) | Domain::U128 | Domain::USize(_) | Domain::ISize(_) => {
                dom.bitvec_order_key(e)?
            }
            // `bool` ordering is rejected before a monitor is built; if reached,
            // the identity leaves a `Nat.ble` over a `Bool` that fails kernel
            // typecheck (a graceful error, never a panic). The Option carrier
            // is unordered for the same reason and takes the same identity, and
            // `int` (which has no runtime carrier at all, so no monitor is ever
            // built for it) joins them rather than inventing an order key.
            Domain::Bool | Domain::Int | Domain::OptionSigned(_) | Domain::RegisteredAdt(_) => e,
        })
    };
    let l = to_nat(elab_term(&b.left, vars, offset, var_domains, dom)?)?;
    let r = to_nat(elab_term(&b.right, vars, offset, var_domains, dom)?)?;
    let (mut small, large) = if swap { (r, l) } else { (l, r) };
    if strict {
        small = nat_succ(small);
    }
    Ok((small, large))
}

/// `(mon_body, cond_true, cond_false)` for an ATOMIC comparison clause (`a <= b`
/// / `<` / `>=` / `>`) at binder `offset`, where
///   `cond_true  = λ (h : mon_body = true).  <proof of P>`  and
///   `cond_false = λ (h : mon_body = false). <proof of ¬P>`
/// (the proof bodies live one binder deeper, so their operands are at
/// `offset+1`). `cond_true` uses `Nat.le_of_ble_eq_true` (soundness);
/// `cond_false` uses `Nat.not_le_of_ble_eq_false` (completeness), which the
/// negation lane consumes. Every comparison uses the single `Nat.ble` bridge
/// (strict `<`/`>` via `Nat.lt a b ≡ Nat.le (succ a) b`).
fn comparison_mon_cond(
    b: &syn::ExprBinary,
    vars: &[String],
    offset: u32,
    dom: &Domain,
) -> Result<(Expr, Expr, Expr), String> {
    let var_domains = uniform_var_domains(vars, dom);
    let (a0, b0) = ble_operands_with_domains(b, vars, offset, &var_domains, dom)?;
    let ble = Expr::const_(Name::interned("Nat.ble"), vec![]);
    let mon_body = Expr::app(Expr::app(ble, a0), b0);
    let (a1, b1) =
        ble_operands_with_domains(b, vars, one_binder_deeper(offset)?, &var_domains, dom)?;
    // cond_true: `Nat.le_of_ble_eq_true a b h : Nat.le a b` (defeq to Nat.lt for
    // strict). cond_false: `Nat.not_le_of_ble_eq_false a b h : ¬(Nat.le a b)`.
    let sound = Expr::const_(Name::interned("Nat.le_of_ble_eq_true"), vec![]);
    let compl = Expr::const_(Name::interned("Nat.not_le_of_ble_eq_false"), vec![]);
    let cond_true = Expr::lam(
        BinderInfo::Default,
        bool_eq_true(mon_body.clone()),
        Expr::apps(sound, [a1.clone(), b1.clone(), Expr::bvar(0)]),
    );
    let cond_false = Expr::lam(
        BinderInfo::Default,
        bool_eq_false(mon_body.clone()),
        Expr::apps(compl, [a1, b1, Expr::bvar(0)]),
    );
    Ok((mon_body, cond_true, cond_false))
}

/// `(mon_body, cond_true, cond_false)` for an ATOMIC equality clause (`a == b`).
///
/// - `Nat`: decides via `Nat.beq`; `cond_true` cites `Nat.eq_of_beq_eq_true`,
///   `cond_false` cites `Nat.ne_of_beq_false`.
/// - `Machine(<Carrier>)`: decides via `decide (Eq <Carrier> a b)` using the
///   wrapper `<Carrier>.decEq` instance; `cond_true`/`cond_false` cite the
///   generic `of_decide_eq_true`/`of_decide_eq_false` bridges. This directly
///   certifies the clause proposition (`Eq <Carrier> a b`) with no bespoke
///   `toNat`-injectivity lemma — if `<Carrier>.decEq` is absent the kernel
///   rejects the certificate and the monitor fails closed.
fn equality_mon_cond(
    b: &syn::ExprBinary,
    vars: &[String],
    offset: u32,
    dom: &Domain,
) -> Result<(Expr, Expr, Expr), String> {
    if !matches!(b.op, BinOp::Eq(_)) {
        return Err("equality monitor: expected `==`".into());
    }
    // MONITOR LANE, SINGLE DOMAIN. `dom` is the atom's one domain (its caller
    // resolved it with `atom_domain` over the whole atom), so the per-variable
    // map is the uniform one — this reproduces the pre-increment typing of
    // every operand exactly.
    let var_domains = uniform_var_domains(vars, dom);
    let var_domains = &var_domains;
    match dom {
        // No decision procedure is minted for `int`: it has no runtime carrier,
        // so there is nothing for a monitor to evaluate. Refused by NAME here
        // rather than reached — `certify_monitor_*` never sees this domain,
        // because a lifted clause is unmonitored.
        Domain::Int => Err("`int` is a kernel-goal-only domain (the nat-lift codomain): it has no executable runtime carrier, so a clause that reaches it is `unmonitored` rather than monitored at a guessed width".into()),
        Domain::Nat => {
            let a0 = elab_term(&b.left, vars, offset, var_domains, dom)?;
            let b0 = elab_term(&b.right, vars, offset, var_domains, dom)?;
            let beq = Expr::const_(Name::interned("Nat.beq"), vec![]);
            let mon_body = Expr::app(Expr::app(beq, a0), b0);
            let a1 = elab_term(&b.left, vars, offset + 1, var_domains, dom)?;
            let b1 = elab_term(&b.right, vars, offset + 1, var_domains, dom)?;
            let sound = Expr::const_(Name::interned("Nat.eq_of_beq_eq_true"), vec![]);
            let compl = Expr::const_(Name::interned("Nat.ne_of_beq_false"), vec![]);
            let cond_true = Expr::lam(
                BinderInfo::Default,
                bool_eq_true(mon_body.clone()),
                Expr::apps(sound, [a1.clone(), b1.clone(), Expr::bvar(0)]),
            );
            let cond_false = Expr::lam(
                BinderInfo::Default,
                bool_eq_false(mon_body.clone()),
                Expr::apps(compl, [a1, b1, Expr::bvar(0)]),
            );
            Ok((mon_body, cond_true, cond_false))
        }
        Domain::Machine(width) => {
            let dec_eq = Expr::const_(Name::interned(width.dec_eq_const()), vec![]);
            let decide = Expr::const_(Name::interned("decide"), vec![]);
            let of_true = Expr::const_(Name::interned("of_decide_eq_true"), vec![]);
            let of_false = Expr::const_(Name::interned("of_decide_eq_false"), vec![]);
            // mon = @decide (Eq Carrier a b) (Carrier.decEq a b)
            let a0 = elab_term(&b.left, vars, offset, var_domains, dom)?;
            let b0 = elab_term(&b.right, vars, offset, var_domains, dom)?;
            let eq_prop0 = dom.eq(a0.clone(), b0.clone());
            let inst0 = Expr::apps(dec_eq.clone(), [a0, b0]);
            let mon_body = Expr::apps(decide, [eq_prop0, inst0]);
            // certificates cite of_decide_* at the same `Eq`/instance, offset+1.
            let a1 = elab_term(&b.left, vars, offset + 1, var_domains, dom)?;
            let b1 = elab_term(&b.right, vars, offset + 1, var_domains, dom)?;
            let eq_prop1 = dom.eq(a1.clone(), b1.clone());
            let inst1 = Expr::apps(dec_eq, [a1, b1]);
            let cond_true = Expr::lam(
                BinderInfo::Default,
                bool_eq_true(mon_body.clone()),
                Expr::apps(of_true, [eq_prop1.clone(), inst1.clone(), Expr::bvar(0)]),
            );
            let cond_false = Expr::lam(
                BinderInfo::Default,
                bool_eq_false(mon_body.clone()),
                Expr::apps(of_false, [eq_prop1, inst1, Expr::bvar(0)]),
            );
            Ok((mon_body, cond_true, cond_false))
        }
        Domain::Signed(_) | Domain::U128 | Domain::USize(_) | Domain::ISize(_) => {
            let width = dom.bitvec_width_expr()?;
            let dec_eq = Expr::const_(Name::interned("BitVec.decEq"), vec![]);
            let decide = Expr::const_(Name::interned("decide"), vec![]);
            let of_true = Expr::const_(Name::interned("of_decide_eq_true"), vec![]);
            let of_false = Expr::const_(Name::interned("of_decide_eq_false"), vec![]);
            let a0 = elab_term(&b.left, vars, offset, var_domains, dom)?;
            let b0 = elab_term(&b.right, vars, offset, var_domains, dom)?;
            let eq_prop0 = dom.eq(a0.clone(), b0.clone());
            let inst0 = Expr::apps(dec_eq.clone(), [width.clone(), a0, b0]);
            let mon_body = Expr::apps(decide, [eq_prop0, inst0]);
            let a1 = elab_term(&b.left, vars, offset + 1, var_domains, dom)?;
            let b1 = elab_term(&b.right, vars, offset + 1, var_domains, dom)?;
            let eq_prop1 = dom.eq(a1.clone(), b1.clone());
            let inst1 = Expr::apps(dec_eq, [width, a1, b1]);
            let cond_true = Expr::lam(
                BinderInfo::Default,
                bool_eq_true(mon_body.clone()),
                Expr::apps(of_true, [eq_prop1.clone(), inst1.clone(), Expr::bvar(0)]),
            );
            let cond_false = Expr::lam(
                BinderInfo::Default,
                bool_eq_false(mon_body.clone()),
                Expr::apps(of_false, [eq_prop1, inst1, Expr::bvar(0)]),
            );
            Ok((mon_body, cond_true, cond_false))
        }
        // Boolean equality decides through `decide (Eq Bool a b)` with
        // `Bool.decEq`, certified by `of_decide_eq_true`/`_false` — the SAME
        // calculus as machine equality, only the `decEq` instance differs.
        Domain::Bool => {
            let a0 = elab_term(&b.left, vars, offset, var_domains, dom)?;
            let b0 = elab_term(&b.right, vars, offset, var_domains, dom)?;
            let a1 = elab_term(&b.left, vars, offset + 1, var_domains, dom)?;
            let b1 = elab_term(&b.right, vars, offset + 1, var_domains, dom)?;
            Ok(bool_eq_mon_cond(a0, b0, a1, b1, dom))
        }
        // No executable equality monitor exists over an Option carrier (there
        // is no runtime carrier at all — see `runtime_domain`): fail closed.
        Domain::RegisteredAdt(_) => Err(dom.registered_operation_refusal("runtime monitoring")),
        Domain::OptionSigned(_) => {
            Err("equality monitors are not supported for an Option carrier".into())
        }
    }
}

/// The certified `decide (Eq Bool a b) + Bool.decEq` equality monitor for two
/// already-elaborated boolean operands (at `offset` and `offset+1`). Shared by
/// `equality_mon_cond` (for `a == b`) and `build_mon_cond`'s bare-boolean arm
/// (which supplies `Bool.true` as the right operand, so `flag ≡ flag == true`).
fn bool_eq_mon_cond(a0: Expr, b0: Expr, a1: Expr, b1: Expr, dom: &Domain) -> (Expr, Expr, Expr) {
    let dec_eq = Expr::const_(Name::interned("Bool.decEq"), vec![]);
    let decide = Expr::const_(Name::interned("decide"), vec![]);
    let of_true = Expr::const_(Name::interned("of_decide_eq_true"), vec![]);
    let of_false = Expr::const_(Name::interned("of_decide_eq_false"), vec![]);
    let eq_prop0 = dom.eq(a0.clone(), b0.clone());
    let inst0 = Expr::apps(dec_eq.clone(), [a0, b0]);
    let mon_body = Expr::apps(decide, [eq_prop0, inst0]);
    let eq_prop1 = dom.eq(a1.clone(), b1.clone());
    let inst1 = Expr::apps(dec_eq, [a1, b1]);
    let cond_true = Expr::lam(
        BinderInfo::Default,
        bool_eq_true(mon_body.clone()),
        Expr::apps(of_true, [eq_prop1.clone(), inst1.clone(), Expr::bvar(0)]),
    );
    let cond_false = Expr::lam(
        BinderInfo::Default,
        bool_eq_false(mon_body.clone()),
        Expr::apps(of_false, [eq_prop1, inst1, Expr::bvar(0)]),
    );
    (mon_body, cond_true, cond_false)
}

/// Recursively build `(mon_body, cond_true, cond_false)` for a clause at binder
/// `offset`, where
///   `cond_true  : (mon_body = true)  → P(clause)`  and
///   `cond_false : (mon_body = false) → ¬P(clause)`,
/// each `λ (h : mon_body = <lit>). <proof>`. Carrying BOTH directions (a
/// decision procedure with soundness AND completeness) is what lets negation
/// recurse through arbitrary structure — `¬(!C)`, `¬(P && Q)`, `¬(P || Q)` — via
/// the De Morgan bridges. Shapes: atomic comparison/equality (leaves), `&&`
/// (`Bool.and` + `and_eq_true_left/right` / `and_eq_false_elim`), `||`
/// (`Bool.or` + `or_eq_true_elim` / `or_eq_false_elim`), `!` (`Bool.not` +
/// `not_eq_true` / `not_eq_false`, flipping the operand's two certificates).
///
/// No explicit de Bruijn lift is ever taken: each arm REBUILDS its sub-clauses
/// one (or more) binders deeper for use under the freshly opened binder(s). The
/// deepest nesting is the `||` completeness case (`offset+3`: the `h`, then the
/// two-argument De Morgan continuation).
fn build_mon_cond(
    ast: &SynExpr,
    vars: &[String],
    offset: u32,
    var_domains: &BTreeMap<String, Domain>,
) -> Result<(Expr, Expr, Expr), String> {
    match ast {
        SynExpr::Paren(p) => build_mon_cond(&p.expr, vars, offset, var_domains),
        SynExpr::Unary(u) if matches!(u.op, syn::UnOp::Not(_)) => {
            // mon = Bool.not mon_C; the clause proposition is `Not C`.
            let (mc0, _, _) = build_mon_cond(&u.expr, vars, offset, var_domains)?;
            let not_c = Expr::const_(Name::interned("Bool.not"), vec![]);
            let mon_body = Expr::app(not_c, mc0);
            // Trust: clean's prelude renamed these Bool negation bridges (FIDELITY /
            // KV-LIFT 2026-07-12) to avoid shadowing Lean 4's `Bool.not_eq_{true,false}`
            // (whose real statements are `Not (b = ·)` Prop-equalities, NOT these
            // `Bool.not b = · → b = ·` implications). Same statement, new names.
            let not_eq_true =
                Expr::const_(Name::interned("Clean.Bool.eq_false_of_not_eq_true"), vec![]);
            let not_eq_false =
                Expr::const_(Name::interned("Clean.Bool.eq_true_of_not_eq_false"), vec![]);
            // cond_true (offset+1): C.cond_false (not_eq_true mc1 h) : ¬C
            let (mc1, _ct1, cf1) = build_mon_cond(&u.expr, vars, offset + 1, var_domains)?;
            let h_false1 = Expr::apps(not_eq_true, [mc1, Expr::bvar(0)]);
            let cond_true = Expr::lam(
                BinderInfo::Default,
                bool_eq_true(mon_body.clone()),
                Expr::app(cf1, h_false1),
            );
            // cond_false: λ h. λ (nc : Not C). nc (C.cond_true (not_eq_false mc2 h))
            // Under `h` then `nc` we are at offset+2; `h` is bvar 1, `nc` is bvar 0.
            let prop_c1 = elaborate_prop_multi(&u.expr, vars, offset + 1, var_domains)?;
            let (mc2, ct2, _cf2) = build_mon_cond(&u.expr, vars, offset + 2, var_domains)?;
            let h_true2 = Expr::apps(not_eq_false, [mc2, Expr::bvar(1)]);
            let c_proof = Expr::app(ct2, h_true2); // : C
            let false_body = Expr::app(Expr::bvar(0), c_proof); // nc c_proof : False
            let nc_lam = Expr::lam(BinderInfo::Default, not_prop(prop_c1), false_body);
            let cond_false =
                Expr::lam(BinderInfo::Default, bool_eq_false(mon_body.clone()), nc_lam);
            Ok((mon_body, cond_true, cond_false))
        }
        SynExpr::Binary(b) if matches!(b.op, BinOp::And(_)) => {
            let (mon_p0, _, _) = build_mon_cond(&b.left, vars, offset, var_domains)?;
            let (mon_q0, _, _) = build_mon_cond(&b.right, vars, offset, var_domains)?;
            let and_c = Expr::const_(Name::interned("Bool.and"), vec![]);
            let mon_body = Expr::apps(and_c, [mon_p0, mon_q0]);
            // ── cond_true (offset+1): and_eq_true_left/right + And.intro ──
            let (mon_p1, ctp1, _cfp1) = build_mon_cond(&b.left, vars, offset + 1, var_domains)?;
            let (mon_q1, ctq1, _cfq1) = build_mon_cond(&b.right, vars, offset + 1, var_domains)?;
            let prop_p1 = elaborate_prop_multi(&b.left, vars, offset + 1, var_domains)?;
            let prop_q1 = elaborate_prop_multi(&b.right, vars, offset + 1, var_domains)?;
            let left_bridge = Expr::const_(Name::interned("Bool.and_eq_true_left"), vec![]);
            let right_bridge = Expr::const_(Name::interned("Bool.and_eq_true_right"), vec![]);
            let hp = Expr::apps(left_bridge, [mon_p1.clone(), mon_q1.clone(), Expr::bvar(0)]);
            let hq = Expr::apps(right_bridge, [mon_p1.clone(), mon_q1.clone(), Expr::bvar(0)]);
            let and_intro = Expr::const_(Name::interned("And.intro"), vec![]);
            let ct_body = Expr::apps(
                and_intro,
                [prop_p1.clone(), prop_q1.clone(), Expr::app(ctp1, hp), Expr::app(ctq1, hq)],
            );
            let cond_true = Expr::lam(BinderInfo::Default, bool_eq_true(mon_body.clone()), ct_body);
            // ── cond_false (offset+1): and_eq_false_elim → case-split → ¬(P∧Q) ──
            // Each case fn opens a binder (hp/hq), so its conjunct is at offset+2.
            let (_, _, cfp2) = build_mon_cond(&b.left, vars, offset + 2, var_domains)?;
            let (_, _, cfq2) = build_mon_cond(&b.right, vars, offset + 2, var_domains)?;
            let prop_p2 = elaborate_prop_multi(&b.left, vars, offset + 2, var_domains)?;
            let prop_q2 = elaborate_prop_multi(&b.right, vars, offset + 2, var_domains)?;
            let neg_and1 = not_prop(connective("And", prop_p1, prop_q1));
            let not_and_left = Expr::const_(Name::interned("not_and_of_not_left"), vec![]);
            let not_and_right = Expr::const_(Name::interned("not_and_of_not_right"), vec![]);
            // fa : (mon_P=false) → ¬(P∧Q) = λ hp. not_and_of_not_left P Q (cfp hp)
            let fa = {
                let neg_p = Expr::app(cfp2, Expr::bvar(0));
                let body = Expr::apps(not_and_left, [prop_p2.clone(), prop_q2.clone(), neg_p]);
                Expr::lam(BinderInfo::Default, bool_eq_false(mon_p1.clone()), body)
            };
            // fb : (mon_Q=false) → ¬(P∧Q) = λ hq. not_and_of_not_right P Q (cfq hq)
            let fb = {
                let neg_q = Expr::app(cfq2, Expr::bvar(0));
                let body = Expr::apps(not_and_right, [prop_p2, prop_q2, neg_q]);
                Expr::lam(BinderInfo::Default, bool_eq_false(mon_q1.clone()), body)
            };
            let and_false_elim = Expr::const_(Name::interned("Bool.and_eq_false_elim"), vec![]);
            let cf_body =
                Expr::apps(and_false_elim, [mon_p1, mon_q1, neg_and1, Expr::bvar(0), fa, fb]);
            let cond_false =
                Expr::lam(BinderInfo::Default, bool_eq_false(mon_body.clone()), cf_body);
            Ok((mon_body, cond_true, cond_false))
        }
        SynExpr::Binary(b) if matches!(b.op, BinOp::Or(_)) => {
            let (mon_p0, _, _) = build_mon_cond(&b.left, vars, offset, var_domains)?;
            let (mon_q0, _, _) = build_mon_cond(&b.right, vars, offset, var_domains)?;
            let or_c = Expr::const_(Name::interned("Bool.or"), vec![]);
            let mon_body = Expr::apps(or_c, [mon_p0, mon_q0]);
            let prop_p1 = elaborate_prop_multi(&b.left, vars, offset + 1, var_domains)?;
            let prop_q1 = elaborate_prop_multi(&b.right, vars, offset + 1, var_domains)?;
            // ── cond_true (offset+1 args, offset+2 case fns): or_eq_true_elim ──
            let (mon_p1, _ctp1, _cfp1) = build_mon_cond(&b.left, vars, offset + 1, var_domains)?;
            let (mon_q1, _ctq1, _cfq1) = build_mon_cond(&b.right, vars, offset + 1, var_domains)?;
            let result_ty = connective("Or", prop_p1.clone(), prop_q1.clone());
            let (_, ctp2, _) = build_mon_cond(&b.left, vars, offset + 2, var_domains)?;
            let (mon_q2, ctq2, _) = build_mon_cond(&b.right, vars, offset + 2, var_domains)?;
            let prop_p2 = elaborate_prop_multi(&b.left, vars, offset + 2, var_domains)?;
            let prop_q2 = elaborate_prop_multi(&b.right, vars, offset + 2, var_domains)?;
            let or_inl = Expr::const_(Name::interned("Or.inl"), vec![]);
            let or_inr = Expr::const_(Name::interned("Or.inr"), vec![]);
            let fa = {
                let inl = Expr::apps(
                    or_inl,
                    [prop_p2.clone(), prop_q2.clone(), Expr::app(ctp2, Expr::bvar(0))],
                );
                Expr::lam(BinderInfo::Default, bool_eq_true(mon_p1.clone()), inl)
            };
            let fb = {
                let inr = Expr::apps(
                    or_inr,
                    [prop_p2.clone(), prop_q2.clone(), Expr::app(ctq2, Expr::bvar(0))],
                );
                Expr::lam(BinderInfo::Default, bool_eq_true(mon_q1.clone()), inr)
            };
            let or_true_elim = Expr::const_(Name::interned("Bool.or_eq_true_elim"), vec![]);
            let ct_body = Expr::apps(
                or_true_elim,
                [mon_p1.clone(), mon_q1.clone(), result_ty, Expr::bvar(0), fa, fb],
            );
            let cond_true = Expr::lam(BinderInfo::Default, bool_eq_true(mon_body.clone()), ct_body);
            // ── cond_false (offset+1): or_eq_false_elim → both false → ¬(P∨Q) ──
            // The continuation `k` opens TWO binders (hp, hq), so the conjuncts are
            // at offset+3: `hp` is bvar 1, `hq` is bvar 0.
            let (_, _, cfp3) = build_mon_cond(&b.left, vars, offset + 3, var_domains)?;
            let (_, _, cfq3) = build_mon_cond(&b.right, vars, offset + 3, var_domains)?;
            let prop_p3 = elaborate_prop_multi(&b.left, vars, offset + 3, var_domains)?;
            let prop_q3 = elaborate_prop_multi(&b.right, vars, offset + 3, var_domains)?;
            let neg_or1 = not_prop(connective("Or", prop_p1, prop_q1));
            let not_or = Expr::const_(Name::interned("not_or_intro"), vec![]);
            let k = {
                let inner = Expr::apps(
                    not_or,
                    [
                        prop_p3,
                        prop_q3,
                        Expr::app(cfp3, Expr::bvar(1)),
                        Expr::app(cfq3, Expr::bvar(0)),
                    ],
                );
                let inner_lam = Expr::lam(BinderInfo::Default, bool_eq_false(mon_q2), inner);
                Expr::lam(BinderInfo::Default, bool_eq_false(mon_p1.clone()), inner_lam)
            };
            let or_false_elim = Expr::const_(Name::interned("Bool.or_eq_false_elim"), vec![]);
            let cf_body = Expr::apps(or_false_elim, [mon_p1, mon_q1, neg_or1, Expr::bvar(0), k]);
            let cond_false =
                Expr::lam(BinderInfo::Default, bool_eq_false(mon_body.clone()), cf_body);
            Ok((mon_body, cond_true, cond_false))
        }
        // `a != b` desugars to `!(a == b)`, reusing the `Bool.not` + equality
        // certificate path above (see `ne_as_not_eq`).
        SynExpr::Binary(b) if matches!(b.op, BinOp::Ne(_)) => {
            build_mon_cond(&ne_as_not_eq(b), vars, offset, var_domains)
        }
        // A DECIDED `bool`-valued operand — a nested comparison, a boolean
        // connective, or a call to an admitted `-> bool` function — is statable
        // in the kernel but has NO executable twin: the runtime monitor
        // evaluates a clause over `u128` scalars and holds no denotation for a
        // kernel-imported constant. Refuse it by SHAPE, naming the real reason.
        // Before this arm the refusal came out of `atom_domain` as "mixed
        // domains in one comparison", which blamed a domain mix that does not
        // exist and put that text in `-Ztrust-verify-output=json`'s
        // `monitor.reason`.
        SynExpr::Binary(b)
            if matches!(
                b.op,
                BinOp::Eq(_) | BinOp::Le(_) | BinOp::Lt(_) | BinOp::Ge(_) | BinOp::Gt(_)
            ) && (decided_bool_form(&b.left, var_domains)
                || decided_bool_form(&b.right, var_domains)) =>
        {
            Err("monitor fragment: a decided `bool`-valued operand (a nested comparison, a \
                 boolean connective, or a call to an admitted `-> bool` function) has no \
                 executable monitor twin"
                .into())
        }
        // Equality / comparison / bare-bool ATOMS take the single domain shared
        // by their variables (`atom_domain`); the connective arms above stay
        // domain-agnostic.
        SynExpr::Binary(b) if matches!(b.op, BinOp::Eq(_)) => {
            equality_mon_cond(b, vars, offset, &atom_domain(ast, var_domains)?)
        }
        // A bare boolean `flag` decides as `flag == true` — the same certified
        // equality monitor with `Bool.true` as the right operand.
        SynExpr::Path(_) => {
            let dom = atom_domain(ast, var_domains)?;
            if !dom.is_bool() {
                return Err(
                    "monitor fragment: expected a comparison, equality, or a `&& || !` of them"
                        .into(),
                );
            }
            let a0 = elab_term(ast, vars, offset, var_domains, &dom)?;
            let a1 = elab_term(ast, vars, offset + 1, var_domains, &dom)?;
            let t0 = dom.bool_lit(true)?;
            let t1 = dom.bool_lit(true)?;
            Ok(bool_eq_mon_cond(a0, t0, a1, t1, &dom))
        }
        SynExpr::Binary(b) => comparison_mon_cond(b, vars, offset, &atom_domain(ast, var_domains)?),
        _ => {
            Err("monitor fragment: expected a comparison, equality, or a `&& || !` of them".into())
        }
    }
}

/// Wrap a monitor and both decision directions into a [`CertifiedMonitor`] and
/// KERNEL-CHECK the required equivalence in `env`.
///
/// `cond_true` proves `mon_body = true → P`; `cond_false` proves
/// `mon_body = false → ¬P`.  The reverse implication `P → mon_body = true`
/// is constructed by an equality-threaded `Bool.casesOn`: the false branch
/// contradicts `P` through `cond_false`, while the true branch is reflexive.
fn wrap_and_grade(
    env: &Environment,
    ast: &SynExpr,
    vars: &[String],
    var_domains: &BTreeMap<String, Domain>,
    mon_body: Expr,
    cond_true: Expr,
    _cond_false: Expr,
) -> Result<CertifiedMonitor, String> {
    let monitor = close_over_lam_multi(vars, mon_body.clone(), var_domains)?;
    let eq_true = bool_eq_true(mon_body);
    let prop = elaborate_prop_multi(ast, vars, 0, var_domains)?;

    // completeness : P → mon_body = true.
    let completeness = {
        // Under hp : P, rebuild the monitor one binder deeper.
        let (mon1, _, _) = build_mon_cond(ast, vars, 1, var_domains)?;
        // The cases motive introduces b after hp. Thread equality from the
        // original monitor to b so the false branch has mon = false.
        let (mon2, _, cond_false2) = build_mon_cond(ast, vars, 2, var_domains)?;
        let motive = Expr::lam(
            BinderInfo::Default,
            Expr::const_(Name::interned("Bool"), vec![]),
            Expr::pi(
                BinderInfo::Default,
                bool_eq_expr(mon2, Expr::bvar(0)),
                bool_eq_true(Expr::bvar(1)),
            ),
        );

        let bool_ty = Expr::const_(Name::interned("Bool"), vec![]);
        let bfalse = Expr::const_(Name::interned("Bool.false"), vec![]);
        let btrue = Expr::const_(Name::interned("Bool.true"), vec![]);
        let eq_refl = Expr::const_(Name::interned("Eq.refl"), vec![Level::succ(Level::zero())]);
        let refl_true = Expr::apps(eq_refl.clone(), [bool_ty.clone(), btrue.clone()]);

        // false branch: λ he : mon=false, False.elim (false=true)
        //   ((cond_false he) hp)
        let false_branch = {
            let contradiction = Expr::app(Expr::app(cond_false2, Expr::bvar(0)), Expr::bvar(1));
            let false_elim = Expr::const_(Name::interned("False.elim"), vec![Level::zero()]);
            let false_eq_true = bool_eq_true(bfalse.clone());
            Expr::lam(
                BinderInfo::Default,
                bool_eq(mon1.clone(), "Bool.false"),
                Expr::apps(false_elim, [false_eq_true, contradiction]),
            )
        };
        // true branch: λ _ : mon=true, rfl.
        let true_branch = Expr::lam(BinderInfo::Default, bool_eq_true(mon1.clone()), refl_true);
        let cases_on = Expr::const_(Name::interned("Bool.casesOn"), vec![Level::zero()]);
        let cases = Expr::apps(cases_on, [motive, mon1.clone(), false_branch, true_branch]);
        let refl_mon = Expr::apps(eq_refl, [bool_ty, mon1]);
        Expr::lam(BinderInfo::Default, prop.clone(), Expr::app(cases, refl_mon))
    };

    let iff_goal =
        Expr::apps(Expr::const_(Name::interned("Iff"), vec![]), [eq_true.clone(), prop.clone()]);
    let iff_proof = Expr::apps(
        Expr::const_(Name::interned("Iff.intro"), vec![]),
        [eq_true, prop, cond_true, completeness],
    );
    let equivalence_goal = close_over_multi(vars, iff_goal, var_domains)?;
    let equivalence_proof = close_over_lam_multi(vars, iff_proof, var_domains)?;

    // Per-variable runtime carriers. The executable projector is context-aware:
    // every comparison atom selects its own carrier, while connectives may
    // combine atoms of different carriers.
    let mut domains = BTreeMap::new();
    for v in vars {
        let d = var_domains.get(v).ok_or_else(|| format!("unbound variable `{v}`"))?;
        domains.insert(v.clone(), d.runtime_domain()?);
    }
    let expr = runtime_monitor_prop(ast, var_domains)?;
    let runtime = RuntimeMonitor { variables: vars.to_vec(), domains, expr };
    match cert_meter::grade(env, &equivalence_goal, &equivalence_proof) {
        Grade::Certified => {
            Ok(CertifiedMonitor { monitor, runtime, equivalence_goal, equivalence_proof })
        }
        Grade::Trusted { closure } => {
            Err(format!("monitor equivalence not Certified (closure: {closure:?})"))
        }
        Grade::Rejected { error } => {
            Err(format!("monitor equivalence rejected by the kernel: {error}"))
        }
    }
}

/// Build a CERTIFIED MONITOR for a single comparison clause (`a <= b`,
/// `a < b`, `a >= b`, `a > b`) over `dom`, and KERNEL-CHECK its soundness
/// certificate in `env`. Comparison-only entry: equality and connectives fail
/// closed here (use [`certify_monitor`] for the structural dispatcher).
pub fn certify_comparison_monitor(
    env: &Environment,
    spec: &str,
    dom: &Domain,
) -> Result<CertifiedMonitor, String> {
    let ast: SynExpr = syn::parse_str(spec).map_err(|e| format!("parse error: {e}"))?;
    let SynExpr::Binary(b) = &ast else {
        return Err("monitor fragment: expected a single comparison".into());
    };
    // Reject equality/connectives — this entry is comparison-only.
    comparison_decision(&b.op)
        .ok_or_else(|| "monitor fragment: only <= < >= > are supported".to_string())?;
    let mut vars = Vec::new();
    collect_vars(&ast, &mut vars);
    let (mon_body, cond_true, cond_false) = comparison_mon_cond(b, &vars, 0, dom)?;
    wrap_and_grade(
        env,
        &ast,
        &vars,
        &uniform_var_domains(&vars, dom),
        mon_body,
        cond_true,
        cond_false,
    )
}

/// Build a CERTIFIED MONITOR for a single equality clause (`a == b`) over the
/// `Nat` domain, and KERNEL-CHECK its soundness certificate in `env`. The
/// Over `Nat` the monitor decides via `Nat.beq` (soundness `Nat.eq_of_beq_eq_true`);
/// over a machine domain it decides via `decide (Eq <Carrier> a b)` with the
/// `<Carrier>.decEq` instance (soundness `of_decide_eq_true`). Both are present
/// in the default prelude by construction. See [`equality_mon_cond`].
pub fn certify_equality_monitor(
    env: &Environment,
    spec: &str,
    dom: &Domain,
) -> Result<CertifiedMonitor, String> {
    let ast: SynExpr = syn::parse_str(spec).map_err(|e| format!("parse error: {e}"))?;
    let SynExpr::Binary(b) = &ast else {
        return Err("monitor fragment: expected a single equality".into());
    };
    let mut vars = Vec::new();
    collect_vars(&ast, &mut vars);
    let (mon_body, cond_true, cond_false) = equality_mon_cond(b, &vars, 0, dom)?;
    wrap_and_grade(
        env,
        &ast,
        &vars,
        &uniform_var_domains(&vars, dom),
        mon_body,
        cond_true,
        cond_false,
    )
}

/// Build a CERTIFIED MONITOR for a clause, dispatching on structure: atomic
/// comparisons (`<= < >= >`), equality (`==`), CONJUNCTIONS (`&&`),
/// DISJUNCTIONS (`||`), and negations (`!P`) over arbitrary propositional
/// subexpressions are certifiable. The `&&` lane certifies
/// `Bool.and mon_P mon_Q = true → P ∧ Q` via the `Bool.and_eq_true_left/right`
/// bridges + `And.intro`; the `||` lane certifies
/// `Bool.or mon_P mon_Q = true → P ∨ Q` via `Bool.or_eq_true_elim` +
/// `Or.inl`/`Or.inr`; the `!` lane certifies `Bool.not mon_C = true → ¬C` via
/// `Clean.Bool.eq_false_of_not_eq_true` + the operand's completeness certificate. Because
/// `build_mon_cond` carries both a soundness and a completeness certificate for
/// every supported shape, negation recurses through arbitrary structure
/// (`!(P && Q)`, `!(P || Q)`, `!!P`) via the De Morgan bridges.
///
/// Certification is fail-closed outside the supported scalar fragment. Examples
/// include a non-propositional term such as `x + y`, a bare identifier outside
/// the `bool` domain, program calls, a variable or zero divisor, and an
/// over-width shift. Bitwise operations and literal shifts are supported by this
/// library, but the compiler's exact query/static-projection bridge does not yet
/// represent them; native clauses using those operators therefore remain
/// explicitly unmonitored rather than gaining authority from source text alone.
pub fn certify_monitor(
    env: &Environment,
    spec: &str,
    dom: &Domain,
) -> Result<CertifiedMonitor, String> {
    let ast: SynExpr = syn::parse_str(spec).map_err(|e| format!("parse error: {e}"))?;
    let mut vars = Vec::new();
    collect_vars(&ast, &mut vars);
    // A single-domain call maps every variable to `dom` — the uniform map makes
    // the multi-domain monitor lane behave identically to the pre-multi code.
    certify_monitor_ast(env, &ast, &vars, &uniform_var_domains(&vars, dom))
}

/// Certify a monitor over a clause whose variables may carry DIFFERENT domains
/// (`flag && x < 10`). Each occurring variable's type is resolved individually;
/// unrelated extra bindings are permitted (the monitor lane's subset rule).
pub fn certify_monitor_multi(
    env: &Environment,
    spec: &str,
    var_types: &[(&str, &str)],
) -> Result<CertifiedMonitor, String> {
    certify_monitor_multi_resolved(env, spec, var_types, None)
}

/// Target-aware form of [`certify_monitor_multi`].
///
/// The explicit `pointer_width` resolves bare `usize`/`isize` bindings to
/// `BitVec 32` or `BitVec 64`.  A pre-resolved spelling that conflicts with
/// the supplied target (for example `usize32` on a 64-bit target) fails closed.
pub fn certify_monitor_typed_for_target(
    env: &Environment,
    spec: &str,
    var_types: &[(&str, &str)],
    pointer_width: TargetPointerWidth,
) -> Result<CertifiedMonitor, String> {
    certify_monitor_multi_resolved(env, spec, var_types, Some(pointer_width))
}

fn certify_monitor_multi_resolved(
    env: &Environment,
    spec: &str,
    var_types: &[(&str, &str)],
    pointer_width: Option<TargetPointerWidth>,
) -> Result<CertifiedMonitor, String> {
    let ast: SynExpr = syn::parse_str(spec).map_err(|e| format!("parse error: {e}"))?;
    let mut vars = Vec::new();
    collect_vars(&ast, &mut vars);
    let var_domains = subset_typed_bindings(&vars, var_types, pointer_width)?;
    certify_monitor_ast(env, &ast, &vars, &var_domains)
}

fn subset_typed_bindings(
    vars: &[String],
    var_types: &[(&str, &str)],
    pointer_width: Option<TargetPointerWidth>,
) -> Result<BTreeMap<String, Domain>, String> {
    let mut var_domains = BTreeMap::new();
    for v in vars {
        let mut matches = var_types.iter().filter(|(name, _)| *name == v.as_str());
        let ty = matches
            .next()
            .map(|(_, ty)| *ty)
            .ok_or_else(|| format!("missing supported type for clause variable `{v}`"))?;
        if matches.next().is_some() {
            return Err(format!("duplicate clause variable binding `{v}`"));
        }
        let d = match pointer_width {
            Some(width) => Domain::from_binding_ty_for_target(ty, width),
            None => Domain::from_binding_ty(ty),
        }
        .ok_or_else(|| {
            let target = pointer_width
                .map(|w| format!(" for a {}-bit target", w.bits()))
                .unwrap_or_default();
            format!("unsupported or target-inconsistent clause variable type `{ty}`{target}")
        })?;
        var_domains.insert(v.clone(), d);
    }
    Ok(var_domains)
}

fn certify_monitor_ast(
    env: &Environment,
    ast: &SynExpr,
    vars: &[String],
    var_domains: &BTreeMap<String, Domain>,
) -> Result<CertifiedMonitor, String> {
    let (mon_body, cond_true, cond_false) = build_mon_cond(ast, vars, 0, var_domains)?;
    wrap_and_grade(env, ast, vars, var_domains, mon_body, cond_true, cond_false)
}

/// Build a CERTIFIED MONITOR for a clause whose free variables carry Rust
/// types (two-language design §1.1). This is the entry a compiler
/// contract-clause sweep calls with the function's COMPLETE parameter
/// signature, so the binding gate is [`certify_monitor_multi`]: every variable
/// occurring in the clause must carry one supported closed carrier (`nat`,
/// `u8`…`u128`, `i8`…`i128`, an explicitly resolved pointer carrier, or
/// `bool`; bare target-dependent, unknown, and duplicate bindings fail closed),
/// while parameters the clause does not
/// mention are permitted and ignored. Distinct variables may carry DIFFERENT
/// carriers (`flag && x < 10`); only a single comparison's operands must
/// agree. The
/// certified result carries the executable runtime payload guarded by its
/// kernel-checked equivalence certificate; it still grants no Rust/Trust-IR
/// proof authority.
pub fn certify_monitor_typed(
    env: &Environment,
    spec: &str,
    var_types: &[(&str, &str)],
) -> Result<CertifiedMonitor, String> {
    // Per-variable domains: this handles both single-domain clauses (every
    // variable resolves to the same carrier) and mixed clauses.
    certify_monitor_multi(env, spec, var_types)
}

/// Certify a clause against a compiler-owned complete binding scope using only
/// the built-in Clean prelude. [`certify_monitor_multi`] selects the exact
/// free-name subset, so unrelated parameters are ignored while missing,
/// duplicate, unsupported, or target-dependent bindings fail closed. Different
/// domains may occur across connective atoms, but one atom must remain
/// homogeneous. The returned carrier remains sealed and executable only
/// because its equivalence proof was kernel accepted.
pub fn certify_monitor_from_typed_scope(
    spec: &str,
    scope_types: &[(&str, &str)],
) -> Result<CertifiedMonitor, String> {
    certify_monitor_typed(&Environment::with_prelude(), spec, scope_types)
}

/// Target-aware built-in-prelude convenience wrapper for
/// [`certify_monitor_typed_for_target`].
pub fn certify_monitor_from_typed_scope_for_target(
    spec: &str,
    scope_types: &[(&str, &str)],
    pointer_width: TargetPointerWidth,
) -> Result<CertifiedMonitor, String> {
    certify_monitor_typed_for_target(&Environment::with_prelude(), spec, scope_types, pointer_width)
}

/// Kernel-bind a scalar term over one explicit domain.
///
/// This is the single-domain counterpart of [`certify_scalar_term_typed`].
/// Every free identifier is bound to `domain`; the returned sealed carrier
/// contains both the checked Clean lambda and its exact runtime evaluator.
pub fn certify_scalar_term(
    env: &Environment,
    spec: &str,
    domain: &Domain,
) -> Result<CertifiedScalarTerm, String> {
    let ast: SynExpr = syn::parse_str(spec).map_err(|e| format!("parse error: {e}"))?;
    let mut vars = Vec::new();
    collect_vars(&ast, &mut vars);
    let var_domains = uniform_var_domains(&vars, domain);
    certify_scalar_term_ast(env, &ast, &vars, &var_domains, domain)
}

/// Kernel-bind a scalar term/measure against a compiler-owned typed scope.
///
/// All variables occurring in the term must resolve to the same non-boolean
/// domain. Unrelated scope entries are ignored; missing, duplicate, mixed,
/// unsupported, or bare target-dependent bindings fail closed.
pub fn certify_scalar_term_typed(
    env: &Environment,
    spec: &str,
    var_types: &[(&str, &str)],
) -> Result<CertifiedScalarTerm, String> {
    certify_scalar_term_typed_resolved(env, spec, var_types, None)
}

/// Target-aware form of [`certify_scalar_term_typed`], resolving bare
/// `usize`/`isize` with an explicit compilation-target pointer width.
pub fn certify_scalar_term_typed_for_target(
    env: &Environment,
    spec: &str,
    var_types: &[(&str, &str)],
    pointer_width: TargetPointerWidth,
) -> Result<CertifiedScalarTerm, String> {
    certify_scalar_term_typed_resolved(env, spec, var_types, Some(pointer_width))
}

fn certify_scalar_term_typed_resolved(
    env: &Environment,
    spec: &str,
    var_types: &[(&str, &str)],
    pointer_width: Option<TargetPointerWidth>,
) -> Result<CertifiedScalarTerm, String> {
    let ast: SynExpr = syn::parse_str(spec).map_err(|e| format!("parse error: {e}"))?;
    let mut vars = Vec::new();
    collect_vars(&ast, &mut vars);
    let var_domains = subset_typed_bindings(&vars, var_types, pointer_width)?;
    let domain = atom_domain(&ast, &var_domains)?;
    certify_scalar_term_ast(env, &ast, &vars, &var_domains, &domain)
}

fn certify_scalar_term_ast(
    env: &Environment,
    ast: &SynExpr,
    vars: &[String],
    var_domains: &BTreeMap<String, Domain>,
    domain: &Domain,
) -> Result<CertifiedScalarTerm, String> {
    if domain.is_bool() {
        return Err("a scalar measure cannot use the `bool` carrier".into());
    }
    let source_body = elab_term(ast, vars, 0, var_domains, domain)?;
    let runtime_expr = runtime_monitor_term(ast, domain, var_domains)?;
    let runtime_body = runtime_scalar_clean_term(&runtime_expr, vars, 0, domain, var_domains)?;
    let kernel_term = close_over_lam_multi(vars, runtime_body.clone(), var_domains)?;

    // The theorem checks the exact carrier, binder types, and agreement of the
    // two independent projections: executable-tree→Clean on the left,
    // source-AST→Clean on the right.
    let binding_atom = domain.eq(runtime_body.clone(), source_body);
    let binding_goal = close_over_multi(vars, binding_atom, var_domains)?;
    let refl = Expr::apps(
        Expr::const_(Name::interned("Eq.refl"), vec![Level::succ(Level::zero())]),
        [domain.ty(), runtime_body],
    );
    let binding_proof = close_over_lam_multi(vars, refl, var_domains)?;

    let mut domains = BTreeMap::new();
    for var in vars {
        let var_domain = var_domains.get(var).ok_or_else(|| format!("unbound variable `{var}`"))?;
        domains.insert(var.clone(), var_domain.runtime_domain()?);
    }
    let runtime = RuntimeScalarTerm {
        variables: vars.to_vec(),
        domains,
        domain: domain.runtime_domain()?,
        expr: runtime_expr,
    };

    match cert_meter::grade(env, &binding_goal, &binding_proof) {
        Grade::Certified => Ok(CertifiedScalarTerm {
            kernel_term,
            runtime,
            domain: domain.clone(),
            binding_goal,
            binding_proof,
        }),
        Grade::Trusted { closure } => {
            Err(format!("scalar-term binding not Certified (closure: {closure:?})"))
        }
        Grade::Rejected { error } => {
            Err(format!("scalar-term binding rejected by the kernel: {error}"))
        }
    }
}

/// E5-facing wrapper for [`certify_scalar_term_typed`].
pub fn certify_measure_typed(
    env: &Environment,
    spec: &str,
    var_types: &[(&str, &str)],
) -> Result<CertifiedMeasure, String> {
    certify_scalar_term_typed(env, spec, var_types)
}

/// Target-aware E5-facing wrapper for
/// [`certify_scalar_term_typed_for_target`].
pub fn certify_measure_typed_for_target(
    env: &Environment,
    spec: &str,
    var_types: &[(&str, &str)],
    pointer_width: TargetPointerWidth,
) -> Result<CertifiedMeasure, String> {
    certify_scalar_term_typed_for_target(env, spec, var_types, pointer_width)
}

/// Prove `goal` through the tactic portfolio (SMT first, then induction) and
/// certify the resulting term through the honesty meter. Returns the winning
/// lane name iff the pair grades `Certified`.
pub fn prove_and_certify(
    env: &Environment,
    engine: &AutomationEngine,
    goal: &Expr,
) -> Result<&'static str, String> {
    let (r, lane) = match engine.auto_prove(env, goal, Duration::from_secs(10), None) {
        Some(r) => (r, "auto"),
        None => match engine.prove_by_induction(env, goal, Duration::from_secs(60)) {
            Some(r) => (r, "induction"),
            None => return Err("no tactic proved the goal".into()),
        },
    };
    match cert_meter::grade(env, goal, r.proof_term()) {
        Grade::Certified => Ok(lane),
        Grade::Rejected { error } => Err(format!("not Certified (rejected: {error})")),
        Grade::Trusted { closure } => Err(format!("not Certified (closure: {closure:?})")),
    }
}

/// Full L1→L5 pipeline on one spec string: elaborate, prove, certify.
pub fn verify_spec(
    env: &Environment,
    engine: &AutomationEngine,
    spec: &str,
) -> Result<&'static str, String> {
    let goal = elaborate_goal(spec)?;
    prove_and_certify(env, engine, &goal)
}

/// Full pipeline on a `requires(pre) ensures(post)` contract: elaborate to
/// `∀ vars, pre → post`, prove, certify.
pub fn verify_contract(
    env: &Environment,
    engine: &AutomationEngine,
    requires: &str,
    ensures: &str,
) -> Result<&'static str, String> {
    let goal = elaborate_contract(requires, ensures)?;
    prove_and_certify(env, engine, &goal)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn checked_binder_indices_preserve_outer_to_inner_order() {
        assert_eq!([0, 1, 2].map(|pos| de_bruijn_index(3, pos, 0).unwrap()), [2, 1, 0],);
        assert_eq!([0, 1, 2].map(|pos| de_bruijn_index(3, pos, 4).unwrap()), [6, 5, 4],);
        assert_eq!(de_bruijn_index(1, 0, 0).unwrap(), 0);
    }

    #[test]
    fn checked_binder_indices_refuse_empty_and_out_of_range_positions() {
        for (len, pos) in [(0, 0), (0, usize::MAX), (3, 3), (3, usize::MAX)] {
            let error = de_bruijn_index(len, pos, 0).unwrap_err();
            assert!(error.contains("binder position"), "{error}");
            assert!(error.contains("outside"), "{error}");
        }
    }

    #[test]
    fn checked_binder_offsets_preserve_maximum_and_refuse_overflow() {
        assert_eq!(de_bruijn_index(1, 0, u32::MAX).unwrap(), u32::MAX);
        assert_eq!(de_bruijn_index(2, 0, u32::MAX - 1).unwrap(), u32::MAX);
        assert_eq!(de_bruijn_index(2, 1, u32::MAX).unwrap(), u32::MAX);
        let error = de_bruijn_index(2, 0, u32::MAX).unwrap_err();
        assert!(error.contains("binder depth 1 +"), "{error}");
        assert!(error.contains("exceeds the kernel's `u32`"), "{error}");
        assert_eq!(one_binder_deeper(u32::MAX - 1).unwrap(), u32::MAX);
        assert!(one_binder_deeper(u32::MAX).is_err());
    }

    #[test]
    #[cfg(target_pointer_width = "64")]
    fn checked_binder_depth_refuses_narrowing_without_allocating_binders() {
        // Exercise the length arithmetic directly: no enormous binder vector
        // is allocated, and a large population does not by itself forbid a
        // representable inner binder.
        let at_limit = usize::try_from(u64::from(u32::MAX) + 1).unwrap();
        assert_eq!(de_bruijn_index(at_limit, 0, 0).unwrap(), u32::MAX);
        assert_eq!(de_bruijn_index(at_limit, at_limit - 1, 0).unwrap(), 0);
        let above_limit = at_limit + 1;
        let error = de_bruijn_index(above_limit, 0, 0).unwrap_err();
        assert!(error.contains("binder depth 4294967296"), "{error}");
        assert!(error.contains("exceeds the kernel's `u32`"), "{error}");
        assert_eq!(de_bruijn_index(above_limit, 1, 0).unwrap(), u32::MAX);
        assert_eq!(de_bruijn_index(above_limit, above_limit - 1, 0).unwrap(), 0);
        assert!(de_bruijn_index(at_limit, 0, 1).is_err());
    }

    #[test]
    fn bool_value_admission_refuses_invalid_domains_and_parameter_indices() {
        let mut env = Environment::with_prelude();
        for (domains, op) in [
            (vec![], BoolValueKind::Not(0)),
            (vec![Domain::Bool], BoolValueKind::Not(1)),
            (vec![Domain::Bool], BoolValueKind::Not(usize::MAX)),
            (vec![Domain::Bool], BoolValueKind::And(0, 1)),
            (vec![Domain::Bool], BoolValueKind::And(usize::MAX, 0)),
            (vec![Domain::Bool], BoolValueKind::Or(1, 0)),
            (vec![Domain::Bool], BoolValueKind::Or(0, usize::MAX)),
            (vec![Domain::Nat], BoolValueKind::Not(0)),
            (vec![Domain::Bool, Domain::Nat], BoolValueKind::And(0, 1)),
        ] {
            let error = admit_bool_value_function(&mut env, "invalid_bool_value", &domains, op)
                .err()
                .expect("invalid Bool carrier/index must refuse before registration");
            assert!(
                error.contains("out of range") || error.contains("must all be `Bool`"),
                "{error}"
            );
            assert!(env.get_const(&Name::from_string("invalid_bool_value")).is_none());
        }
    }

    #[test]
    fn bool_value_admission_preserves_exact_outer_to_inner_binder_order() {
        let mut env = Environment::with_prelude();
        let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
        // Expected indices are independent literals, not the helper under test.
        // In particular, commutative connective truth tables cannot detect a
        // swapped operand, so also compare the exact stored defining equation.
        for (name, op, head, indices) in [
            ("bool_first", BoolValueKind::Not(0), "Bool.not", vec![2]),
            ("bool_middle", BoolValueKind::Not(1), "Bool.not", vec![1]),
            ("bool_last", BoolValueKind::Not(2), "Bool.not", vec![0]),
            ("bool_outer_and_last", BoolValueKind::And(0, 2), "Bool.and", vec![2, 0]),
            ("bool_last_or_middle", BoolValueKind::Or(2, 1), "Bool.or", vec![0, 1]),
        ] {
            let admission = admit_bool_value_function(
                &mut env,
                name,
                &[Domain::Bool, Domain::Bool, Domain::Bool],
                op,
            )
            .unwrap();
            assert!(admission.status().is_reflected());
            assert_eq!(admission.return_domain(), Some(&Domain::Bool));
            let body = Expr::apps(
                Expr::const_(Name::from_string(head), vec![]),
                indices.into_iter().map(Expr::bvar),
            );
            let expected =
                (0..3).fold(body, |body, _| Expr::lam(BinderInfo::Default, bool_ty.clone(), body));
            assert_eq!(
                env.get_const(&Name::from_string(name)).unwrap().value.as_ref(),
                Some(&expected),
                "{name}: the defining equation must retain exact parameter identity"
            );
        }
    }

    #[test]
    fn bool_value_admission_reduces_the_complete_not_and_or_truth_tables() {
        let mut env = Environment::with_prelude();
        admit_bool_value_function(&mut env, "bool_neg", &[Domain::Bool], BoolValueKind::Not(0))
            .unwrap();
        for (name, op) in
            [("bool_conj", BoolValueKind::And(0, 1)), ("bool_disj", BoolValueKind::Or(0, 1))]
        {
            admit_bool_value_function(&mut env, name, &[Domain::Bool, Domain::Bool], op).unwrap();
        }
        let tc = clean_kernel::TypeChecker::new(&env);
        let lit = |value| Domain::Bool.bool_lit(value).unwrap();
        let app =
            |name, args: Vec<Expr>| Expr::apps(Expr::const_(Name::from_string(name), vec![]), args);
        for a in [false, true] {
            assert!(tc.is_def_eq(&app("bool_neg", vec![lit(a)]), &lit(!a)));
            for b in [false, true] {
                assert!(tc.is_def_eq(&app("bool_conj", vec![lit(a), lit(b)]), &lit(a && b)));
                assert!(tc.is_def_eq(&app("bool_disj", vec![lit(a), lit(b)]), &lit(a || b)));
            }
        }
    }

    /// R4 §2 pin: the binder-typing probe's three outcome classes on real
    /// clause shapes. A same-typed comparison against a u64 parameter pins
    /// the binder uniquely; a parameter-free numeric body elaborates under
    /// several typings (ambiguous — a caller must refuse, not pick); nonsense
    /// bodies elaborate under none. The vector always covers exactly the E3
    /// closed set, in order.
    #[test]
    fn untyped_binder_probe_reports_unique_ambiguous_and_none() {
        let unique = probe_untyped_binder_typings("forall", "i", "i <= n", &[("n", "u64")]);
        assert_eq!(unique.len(), E3_BINDER_TYPES.len());
        let successes: Vec<&str> = unique.iter().filter(|(_, ok)| *ok).map(|(ty, _)| *ty).collect();
        assert_eq!(successes, vec!["u64"], "cross-type comparison must pin the binder");

        let ambiguous = probe_untyped_binder_typings("forall", "i", "i >= i", &[]);
        let hits = ambiguous.iter().filter(|(_, ok)| *ok).count();
        assert!(hits > 1, "a parameter-free reflexive body is ambiguous: {ambiguous:?}");

        let none = probe_untyped_binder_typings("exists", "i", "i && (i + no_such)", &[]);
        assert!(none.iter().all(|(_, ok)| !ok), "an ill-formed body admits no typing: {none:?}");
    }

    #[test]
    fn collect_vars_visits_call_and_method_arguments() {
        // E6 STEP 0 seam fix: a variable occurring ONLY inside a call/method
        // argument must still be in the free-variable set; the callee/method
        // name must NOT be.
        let call: SynExpr = syn::parse_str("min(x, y) <= x").unwrap();
        let mut vars = Vec::new();
        collect_vars(&call, &mut vars);
        assert!(vars.contains(&"x".to_string()), "{vars:?}");
        assert!(vars.contains(&"y".to_string()), "y occurs only inside the call arg: {vars:?}");
        assert!(!vars.contains(&"min".to_string()), "callee name is not a variable: {vars:?}");

        let method: SynExpr = syn::parse_str("v.get(i) <= n").unwrap();
        let mut mvars = Vec::new();
        collect_vars(&method, &mut mvars);
        assert!(mvars.contains(&"v".to_string()), "receiver: {mvars:?}");
        assert!(mvars.contains(&"i".to_string()), "method arg: {mvars:?}");
        assert!(mvars.contains(&"n".to_string()), "{mvars:?}");
        assert!(!mvars.contains(&"get".to_string()), "method name is not a variable: {mvars:?}");

        // Nested: a var only inside a call inside a call is still reached.
        let nested: SynExpr = syn::parse_str("f(g(z)) <= w").unwrap();
        let mut nvars = Vec::new();
        collect_vars(&nested, &mut nvars);
        assert!(nvars.contains(&"z".to_string()), "doubly-nested call arg: {nvars:?}");
        assert!(nvars.contains(&"w".to_string()), "{nvars:?}");
    }

    #[test]
    fn exact_clause_bindings_drop_unrelated_signature_entries() {
        let available = [("x", "u64"), ("unused", "bool"), ("y", "u64"), ("result", "u64")];
        assert_eq!(
            exact_typed_bindings_for_clause("y <= x", &available).unwrap(),
            [("y".to_string(), "u64".to_string()), ("x".to_string(), "u64".to_string())],
        );
        assert!(exact_typed_bindings_for_clause("0 == 0", &available).unwrap().is_empty());
        assert_eq!(
            exact_typed_bindings_for_clause("f(x) == result", &available).unwrap(),
            [("x".to_string(), "u64".to_string()), ("result".to_string(), "u64".to_string())],
            "callee identities are not variable bindings, but call arguments are",
        );
        assert_eq!(
            exact_typed_bindings_for_clause("forall i: u64, i <= y", &available).unwrap(),
            [("y".to_string(), "u64".to_string())],
            "a quantified clause selects only its free function parameter",
        );
    }

    #[test]
    fn exact_clause_bindings_fail_closed_on_missing_or_ambiguous_names() {
        assert!(
            exact_typed_bindings_for_clause("x == y", &[("x", "u64")])
                .unwrap_err()
                .contains("missing supported type")
        );
        assert!(
            exact_typed_bindings_for_clause(
                "x == x",
                &[("x", "u64"), ("x", "u64"), ("unused", "bool")],
            )
            .unwrap_err()
            .contains("duplicate clause variable binding")
        );
        let err = exact_typed_bindings_for_clause("forall i: u64, i <= i", &[("i", "u64")])
            .expect_err("a quantified helper must not erase a shadowed signature binding");
        assert!(err.contains("shadows"), "shadowing must fail closed: {err}");
    }

    #[test]
    fn elaborates_and_certifies() {
        let env = Environment::with_prelude();
        let engine = AutomationEngine::new();
        for spec in
            ["x + 0 == x", "0 + x == x", "x + y == x + y", "x * 0 == 0", "x + y == y + x", "x <= x"]
        {
            verify_spec(&env, &engine, spec).unwrap_or_else(|e| panic!("`{spec}`: {e}"));
        }
    }

    #[test]
    fn gradient_total_elaboration_gradual_proof() {
        let env = Environment::with_prelude();
        let engine = AutomationEngine::new();
        // Elaboration is TOTAL: the goal is well-typed.
        assert!(elaborate_goal("0 <= x").is_ok(), "elaboration must be total");
        // Proof is GRADUAL: `0 <= x` is outside the auto-fragment → Pending,
        // not Certified.
        assert!(
            verify_spec(&env, &engine, "0 <= x").is_err(),
            "0<=x must not auto-Certify (it needs deeper tactics)"
        );
    }

    #[test]
    fn contracts_assume_pre_prove_post() {
        let env = Environment::with_prelude();
        let engine = AutomationEngine::new();
        // Sound: the precondition discharges the postcondition.
        verify_contract(&env, &engine, "x <= y", "x <= y").expect("identity contract must certify");
        // Soundness: an unsound postcondition is declined (never a false
        // Certified).
        assert!(verify_contract(&env, &engine, "x <= y", "y <= x").is_err());
    }

    #[test]
    fn fails_closed_out_of_fragment() {
        // Division/remainder by a VARIABLE is outside the fragment (a positive
        // literal divisor is required) — see
        // `division_by_nonliteral_or_zero_fails_closed`. (Bit-shift by a literal
        // IS in the fragment now: `bit_shifts_certify`.)
        assert!(elaborate_goal("x / y == z").is_err());
        assert!(elaborate_goal("x && y").is_err()); // bare operands are not propositions
    }

    #[test]
    fn connectives_elaborate() {
        // && → And, || → Or, ! → Not: elaboration is total over well-formed
        // structure.
        assert!(elaborate_goal("x + 0 == x && x * 0 == 0").is_ok());
        assert!(elaborate_goal("x <= x || x < x").is_ok());
        assert!(elaborate_goal("!(x < x)").is_ok());
    }
}

/// The Clean CARRIER TYPE a clause term inhabits — the kernel's `Nat`, `Bool`,
/// `UInt8..64`, `BitVec N`, or `Option <carrier>`, as a comparable shape.
///
/// WHY THIS IS NOT A [`Domain`]. `Domain -> Carrier` is MANY-TO-ONE: `BitVec 64`
/// is the carrier of `i64`, of `usize` on a 64-bit target and of `isize` on one,
/// and `BitVec 128` is the carrier of both `i128` and `u128`. That is exactly
/// the non-injectivity documented at
/// `trust_certify::clean_island::island_definition_signature`, and it is why
/// reading a `Domain` back off a declared Clean type is forbidden: the two
/// preimages of `BitVec 64` disagree about which literals are in range
/// (`Domain::numeral` caps `i64` at 2^63-1 and `usize64` at 2^64-1), so a guess
/// could admit a literal at a carrier its author never wrote.
///
/// A `Carrier` therefore travels in ONE direction only. It is produced from an
/// AUTHORITATIVE declaration (an island's kernel-recorded Pi telescope, or a
/// compiler mint's own `Domain`s) and consumed only to CHECK a `Domain` that
/// some other authority — the Rust signature behind a clause binding — already
/// fixed. It is never inverted into a `Domain`, and nothing picks a default.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Carrier {
    /// The kernel's unbounded `Nat`.
    Nat,
    /// The kernel's unbounded `Int`.
    Int,
    /// `Bool`.
    Bool,
    /// `UInt8` / `UInt16` / `UInt32` / `UInt64` — the wrapping unsigned carriers.
    UInt(MachineUIntWidth),
    /// `BitVec N`.
    BitVec(u32),
    /// `Option <inner>`.
    Option(Box<Carrier>),
    /// Exact registered family, ordered schema and instantiated arguments.
    RegisteredAdt(RegisteredAdt),
}

impl Carrier {
    /// The UNIQUE [`Domain`] whose carrier is this one, or `None` when there is
    /// more than one — the PARTIAL inverse of `Domain::carrier`.
    ///
    /// This is the one place the map is ever read backwards, and it is defined
    /// exactly where doing so is not a choice: `Nat`, `Bool`, each `UIntN` and
    /// `Option (BitVec N)` have a single preimage apiece. `BitVec N` has three
    /// (`iN`, `usize`, `isize` at that width) and answers `None`, because the
    /// preimages DISAGREE about behaviour a clause can observe —
    /// [`Domain::numeral`] caps `i64` at 2^63-1 and `usize64` at 2^64-1, and
    /// [`Domain::bitvec_order_key`] flips the sign bit for one and not the
    /// other. Picking one would retype an author's carrier; that is the
    /// injectivity caveat recorded at
    /// `trust_certify::clean_island::island_definition_signature`, and this
    /// function is its enforcement rather than an exception to it.
    ///
    /// A new [`Carrier`] variant must decide here explicitly; `None` is always
    /// the safe answer, because every caller falls back to what it did before
    /// the carrier existed.
    #[must_use]
    pub fn unique_domain(&self) -> Option<Domain> {
        match self {
            Carrier::RegisteredAdt(carrier) => Some(Domain::RegisteredAdt(carrier.clone())),
            Carrier::Nat => Some(Domain::Nat),
            // `Int` has exactly one preimage, [`Domain::Int`]: no machine
            // domain carries `Int` (the signed ones carry `BitVec N`), so this
            // is as unambiguous as the `Nat` row above it.
            Carrier::Int => Some(Domain::Int),
            Carrier::Bool => Some(Domain::Bool),
            Carrier::UInt(width) => Some(Domain::Machine(*width)),
            Carrier::BitVec(_) => None,
            // `Option (BitVec N)` is the carrier of `Domain::OptionSigned(N)`
            // and of nothing else: there is no unsigned Option domain. THE DAY
            // one is added this arm must answer `None`, exactly as the bare
            // `BitVec` arm above already does.
            Carrier::Option(inner) => match inner.as_ref() {
                Carrier::BitVec(bits) => Some(Domain::OptionSigned(match bits {
                    8 => MachineSIntWidth::I8,
                    16 => MachineSIntWidth::I16,
                    32 => MachineSIntWidth::I32,
                    64 => MachineSIntWidth::I64,
                    128 => MachineSIntWidth::I128,
                    _ => return None,
                })),
                _ => None,
            },
        }
    }

    /// How the carrier is spelled in Clean, for diagnostics only.
    #[must_use]
    pub fn clean_name(&self) -> String {
        match self {
            Carrier::RegisteredAdt(carrier) => format!("{} {:?}", carrier.name(), carrier.arguments()),
            Carrier::Nat => "Nat".to_string(),
            Carrier::Int => "Int".to_string(),
            Carrier::Bool => "Bool".to_string(),
            Carrier::UInt(width) => width.carrier().to_string(),
            Carrier::BitVec(bits) => format!("BitVec {bits}"),
            Carrier::Option(inner) => format!("Option ({})", inner.clean_name()),
        }
    }

    fn validate_in(&self, env: &Environment) -> Result<(), String> {
        match self {
            Carrier::RegisteredAdt(carrier) => carrier.validate_in(env),
            Carrier::Option(inner) => inner.validate_in(env),
            _ => Ok(()),
        }
    }
}

/// The CALLEE-DECLARED Clean carrier types of an admitted constant: one per
/// value parameter, in application order, plus the result's.
///
/// The whole point of the record is that it comes from the AUTHORITY that
/// declared the constant — the kernel's own recorded type for an island
/// definition, the mint's own parameter domains for a compiler-minted program
/// function — and never from re-reading the Rust side and assuming the two
/// agree. See [`Admission::carriers`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DeclaredCarriers {
    /// One carrier per value parameter, in the order the constant takes them.
    pub params: Vec<Carrier>,
    /// The carrier of the constant's result.
    pub ret: Carrier,
}

impl DeclaredCarriers {
    /// The carriers of a COMPILER MINT, read off the very `Domain`s the mint
    /// used to build the declaration it just handed the kernel.
    ///
    /// This is authoritative for the same reason the mint is: `params` and
    /// `ret` are the exact values passed to `Expr::arrow`/`Expr::lam` a few
    /// lines above every call site, so the record cannot drift from the type
    /// the kernel accepted. It is a re-reading of the mint's own decision, not
    /// an inference from the Rust surface.
    #[must_use]
    pub fn of_domains(params: &[Domain], ret: &Domain) -> Self {
        DeclaredCarriers { params: params.iter().map(Domain::carrier).collect(), ret: ret.carrier() }
    }
}

/// The clause-VARIABLE name an atom denotes, or `None` for any other shape.
///
/// Two spellings are variables, and only these two:
///
///   * a bare identifier — `x`;
///   * a DEPTH-1 NAMED FIELD PROJECTION of a bare identifier — `c.degree`
///     (E6/E9 widening increment 7, "dotted-path scalar binders").
///
/// A dotted path is ONE OPAQUE SCALAR ATOM. The elaborator gives it a binder of
/// the field's own declared carrier and NEVER looks inside the aggregate: the
/// goal it builds is `∀ (c.degree : UInt64) …`, which is WEAKER than the truth
/// (the real `c.degree` is one particular value), so a theorem proving the ∀
/// proves the instance. Nothing here reflects the struct, and no aggregate ever
/// reaches the kernel — that is the separate `reflect_struct` carrier lane.
///
/// The spelling must agree BYTE-FOR-BYTE with the compiler's
/// `trust_fn_param_type_names`, which is the sole producer of the `(name, type)`
/// rows these names are looked up in; a name this function invents that the
/// compiler never emits simply fails the exact-binding gate (fail closed).
///
/// FAIL CLOSED on every richer shape: a nested projection (`c.a.b`), a TUPLE
/// index (`c.0`), a parenthesized base (`(c).degree`), a projection off a call
/// (`f(x).y`), and a multi-segment path (`m::x`). Each returns `None`, collects
/// no variable, and is refused with a named reason by [`elab_term`] — never
/// guessed at, and never silently dropped into a variable-free atom.
fn atom_var_name(e: &SynExpr) -> Option<String> {
    match e {
        SynExpr::Path(p) => p.path.get_ident().map(|id| id.to_string()),
        SynExpr::Field(f) => {
            // A TUPLE index (`syn::Member::Unnamed`) is deliberately outside
            // this increment: the compiler side names rows from the ADT's
            // declared field names, so there is no `c.0` row to bind against.
            let syn::Member::Named(field) = &f.member else {
                return None;
            };
            // The base must be a BARE identifier — the projection is depth 1.
            // `c.a.b` would need the struct carrier to mean anything, and a
            // parenthesized or computed base has no parameter identity.
            let SynExpr::Path(base) = &*f.base else {
                return None;
            };
            let base = base.path.get_ident()?;
            Some(format!("{base}.{field}"))
        }
        _ => None,
    }
}

/// Whether one `::`-separated def-path segment is a plain Rust identifier —
/// i.e. contains nothing (`<`, `>`, `{`, `#`, spaces, generic-argument lists)
/// that would make the segment unspellable in a clause's call position.
fn plain_ident(segment: &str) -> bool {
    let mut chars = segment.chars();
    matches!(chars.next(), Some(c) if c.is_alphabetic() || c == '_')
        && chars.all(|c| c.is_alphanumeric() || c == '_')
}

/// The identity under which the ENSURES-DISCHARGE lane must look the
/// contracted function itself up in the [`FacetTable`] — the key that binds
/// `result` to that function's imported defining equation.
///
/// The canonical def-path when it is a plain identifier path, the LAST segment
/// otherwise.
///
/// Why the def-path and not the bare name (the pre-2026-08-26 identity). The
/// facet/admission record for an item is keyed by `record_fn_facets` under its
/// canonical def-path AND under every [`spec_spellings`] suffix, with ONE
/// collision rule over the whole keyspace: two def-paths under one key evict it
/// and block it forever. That rule is what makes an ambiguous BARE spelling
/// written by a clause author fail closed, and it is correct. But the
/// contracted function's OWN identity is not a spelling an author wrote — the
/// compiler knows exactly which item carries the contract — so deriving it from
/// `tcx.item_name` threw that knowledge away and re-entered the ambiguity
/// keyspace through the one door it did not need. A function whose bare name is
/// shared (`veripb_core_proved::cap_coeff` beside `CoeffDomain::cap_coeff` and
/// its four impls) then could NEVER bind `result`, even though its def-path key
/// survives eviction and its facet record is perfectly good:
/// [`elaborate_ensures`] bailed before building a goal and the clause was
/// silently checked against the forall-over-`result` reading, which is
/// generally false. Keying on the def-path uses the identity the compiler
/// already has.
///
/// SOUNDNESS. This confers no authority: it selects a LOOKUP KEY, and the key
/// must still resolve to an admitted record (certified facets + a minted
/// kernel constant) or the discharge fails closed exactly as before. The
/// def-path is registered through the same owner/eviction lane as every
/// spelling, so a def-path that ever collided with another item's key is
/// evicted too and this lookup fails closed. Nothing here weakens eviction: a
/// clause's own CALLEE spellings are still resolved by `callee_path`, are
/// untouched, and an ambiguous bare callee still has no record.
///
/// A non-identifier def-path (a qualified-impl head `<i64 as
/// lib::CoeffDomain>::cap_coeff`, a generic-argument list, a `{closure#0}`
/// segment) is NOT usable as a self identity even though it is a valid table
/// key: [`elaborate_ensures`] builds the substitute for `result` by parsing
/// `self_fn(params…)` as Rust and the elaborator re-derives the callee key with
/// `callee_path`, which drops the qself — so `<i64 as T>::f` would re-key as
/// `T::f` and could collide with a DIFFERENT item that genuinely has that
/// def-path. Such paths therefore keep the historical last-segment identity,
/// which is subject to eviction and hence fails closed when ambiguous. The
/// round-trip is additionally re-checked inside [`elaborate_ensures`], so a
/// key that cannot reproduce itself through the parser is refused rather than
/// silently re-keyed.
#[must_use]
pub fn self_fn_spelling(def_path: &str) -> String {
    if !def_path.is_empty() && def_path.split("::").all(plain_ident) {
        def_path.to_string()
    } else {
        def_path.rsplit("::").next().unwrap_or(def_path).to_string()
    }
}

/// Every SPELLING of `def_path` a spec clause could plausibly write for the
/// same item, shortest-suffix first and EXCLUDING the full def-path itself
/// (which the caller keys separately) — e.g. `lib::guard::narrow` yields
/// `["narrow", "guard::narrow"]`.
///
/// Why more than the bare name (the pre-2026-08-26 keying). A clause names a
/// function by a Rust path, and the only two spellings the facet table used to
/// hold were the extracted def-path (`lib::guard::narrow`, which no clause
/// writes) and its LAST segment (`narrow`). A crate whose bare name is shared
/// by several items — `guard::narrow` alongside the `CoeffDomain::narrow`
/// trait-impl methods in `veripb-core-proved` — therefore had its only
/// spellable key evicted as ambiguous, and NO spelling of the free function
/// could reach its record even though the item is uniquely determined by
/// `guard::narrow`. Intermediate suffixes close exactly that gap.
///
/// SOUNDNESS: this function is a pure spelling enumeration and confers no
/// authority. It is the CALLER's obligation to apply the same per-key
/// collision eviction to every spelling it returns that the bare name already
/// receives — two def-paths sharing a spelling must evict it, so a spelling
/// key never resolves to one of several candidate items. Longer suffixes are
/// strictly more discriminating than the bare name, so a spelling that
/// survives eviction identifies exactly one item.
///
/// Only a def-path whose segments are ALL plain identifiers contributes
/// intermediate suffixes. A qualified-impl head (`<i64 as lib::CoeffDomain>::
/// narrow`), a generic-argument list (`::<T>`), or any other non-identifier
/// character would otherwise mint keys like `CoeffDomain>::narrow` that no
/// Rust source can spell. Such a path still contributes its LAST segment,
/// because that name IS spellable and its collision against other items of
/// the same name must keep being detected.
#[must_use]
pub fn spec_spellings(def_path: &str) -> Vec<String> {
    let segments: Vec<&str> = def_path.split("::").collect();
    // A single-segment def-path is already keyed under itself; it has no
    // proper suffix to add.
    if segments.len() < 2 || !plain_ident(segments[segments.len() - 1]) {
        return Vec::new();
    }
    let mut spellings = vec![segments[segments.len() - 1].to_string()];
    if segments.iter().all(|s| plain_ident(s)) {
        // Proper suffixes only: `start == 0` is the full def-path.
        for start in (1..segments.len() - 1).rev() {
            spellings.push(segments[start..].join("::"));
        }
    }
    spellings
}

/// Mint an E6 [`Admission`] for a SIGNED CONSTANT function — a nullary function
/// whose body is a single signed machine-integer literal, e.g.
/// `fn zero() -> i64 { 0 }`, `fn one() -> i128 { 1 }`, `fn lo() -> i32 { -7 }`
/// (recognized as `trust_types::admissible_body::AdmissibleBody::ConstantInt`).
/// The signed sibling of [`admit_constant_function`], and the whole content of
/// the signed-constant increment.
///
/// THE SPELLING IS THE POINT. The minted body is the term the CLAUSE
/// elaborator ([`elab_term`]) produces for that same literal at that same
/// width, arm for arm — because the only value a mint has is that a clause
/// mentioning the constant elaborates to a syntactically identical term and
/// `Eq.refl` closes the discharge:
///
///   * `0` takes [`Domain::zero`] (`BitVec.ofNat N Nat.zero`), NOT
///     `numeral(0)`. `elab_term` special-cases `0` to `dom.zero()`, and the
///     comparison / bool-binary / checked mints already mirror that special case;
///     minting `BitVec.ofNat N (nat_lit 0)` instead would rely on the two
///     `Nat` spellings being interchangeable rather than identical.
///   * a POSITIVE literal takes [`Domain::numeral`], which range-checks it
///     against `2^(N-1) - 1` and fails closed above it.
///   * a NEGATIVE literal takes [`Domain::negative_numeral`] on its
///     MAGNITUDE, which range-checks against `2^(N-1)` — so `iN::MIN` is in
///     range and one below it is refused — and emits the two's-complement
///     bit pattern `(0 - magnitude) mod 2^N`. The magnitude is taken with
///     `i128::unsigned_abs`, which is exact at `i128::MIN` where `-value`
///     would overflow.
///
/// SOUNDNESS: `add_decl` FULL-KERNEL-CHECKS the value against the `BitVec N`
/// carrier type and records the defining equation; a mistaken term is
/// REJECTED, never admitted, and an out-of-range literal fails closed BEFORE
/// the kernel. Fidelity of "this function really returns that literal" is the
/// recognizer's job (see `AdmissibleBody::ConstantInt`), including the width,
/// which a `ConstValue::Int` does not carry.
pub fn admit_signed_constant_function(
    env: &mut Environment,
    kernel_const: &str,
    value: i128,
    width: MachineSIntWidth,
) -> Result<Admission, String> {
    let domain = Domain::Signed(width);
    // Exactly `elab_term`'s three-way literal routing, so the mint and a
    // clause mentioning the same literal produce the SAME term.
    let body = if value == 0 {
        domain.zero()
    } else if value > 0 {
        domain.numeral(value.unsigned_abs())? // range-checked, fails closed
    } else {
        // `unsigned_abs` is exact at `i128::MIN`, where `-value` overflows.
        domain.negative_numeral(value.unsigned_abs())? // range-checked, fails closed
    };
    let ty = domain.ty(); // the exact two's-complement carrier, e.g. BitVec 64
    env.add_decl(Declaration::Definition {
        name: Name::from_string(kernel_const),
        level_params: vec![],
        type_: ty,
        value: body,
        is_reducible: true,
    })
    .map_err(|e| format!("kernel rejected the signed-constant defining equation: {e:?}"))?;
    let carriers = DeclaredCarriers::of_domains(&[], &domain);
    Ok(Admission::reflected(kernel_const, 0)
        .with_declared_signature(Some(domain), Some(carriers)))
}

/// Mint an E6 [`Admission`] for a FIELD-PROJECTION function — one whose body
/// reads a scalar field of a by-value aggregate parameter and returns it, e.g.
/// `fn degree_of(c: Cst) -> u64 { c.degree }` (E6/E9 widening increment 7).
///
/// THE KERNEL SEES NO AGGREGATE. The function is minted over its FLATTENED
/// scalar parameter list — one binder per scalar field of every parameter, in
/// declaration order — so `degree_of` above becomes
/// `fun (degree : UInt64) (coeff : UInt64) => degree`, exactly the term
/// [`admit_projection_function`] already builds and the kernel already checks.
/// The struct is a purely compiler-side notion: it decides WHICH binders exist
/// and in WHAT ORDER, and nothing else. That is why this needs no
/// `reflect_struct` carrier and no new kernel vocabulary.
///
/// FAITHFULNESS rests on two facts the caller must have established, and this
/// function re-checks neither (it cannot see the MIR):
///   1. the body genuinely returns that field verbatim — the recognizer's job
///      (`trust_types::admissible_body::AdmissibleBody::FieldProjection`);
///   2. `param_names` and `param_domains` are the SAME flattening, in the same
///      order, that the compiler's clause-side parameter table produces.
///
/// (2) is the one this increment cannot establish by construction, because the
/// two lists are computed twice from two different representations (HIR types
/// and extracted-IR types). So it is not assumed: the flattened names are
/// RECORDED in [`Admission::param_names`] and [`elaborate_ensures`] refuses any
/// clause whose own parameter list differs. A silently reordered flattening
/// then declines to discharge instead of proving the wrong field's theorem.
pub fn admit_field_projection_function(
    env: &mut Environment,
    kernel_const: &str,
    param_domains: &[Domain],
    param_names: &[String],
    return_param: usize,
) -> Result<Admission, String> {
    if param_names.len() != param_domains.len() {
        return Err(format!(
            "field-projection mint: {} flattened parameter name(s) but {} domain(s)",
            param_names.len(),
            param_domains.len()
        ));
    }
    // Duplicate names would make the clause-side bijection gate ambiguous about
    // which binder a dotted path refers to; refuse rather than pick one.
    let unique: BTreeSet<&String> = param_names.iter().collect();
    if unique.len() != param_names.len() {
        return Err("field-projection mint: the flattened parameter names are not unique".into());
    }
    let mut admission = admit_projection_function(env, kernel_const, param_domains, return_param)?;
    admission.param_names = Some(param_names.to_vec());
    Ok(admission)
}

/// One operand of the comparison [`admit_comparison_function`] mints: a source
/// PARAMETER by 0-based index, or an integer LITERAL.
///
/// The compiler-side twin is `trust_types::admissible_body::CmpOperand`; this
/// crate deliberately carries its own copy rather than depending on
/// `trust-types` (see [`admit_expr_function`]'s note on the same boundary).
/// A negative literal is carried by MAGNITUDE, not as a wrapped bit pattern, so
/// `-1` and `u128::MAX` can never be the same operand and the range check
/// happens against the carrier the mint actually has.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CmpOperand {
    /// A 0-based source parameter.
    Param(usize),
    /// A non-negative integer literal.
    Const(u128),
    /// A negative integer literal, by magnitude.
    NegConst(u128),
}

/// The `(proposition, Decidable instance)` pair one machine-integer comparison
/// decides — the shared decision vocabulary of [`admit_select_function`] (as an
/// `ite` scrutinee) and [`admit_comparison_function`] (as a `Decidable.decide`
/// value). `l`/`r` are carrier-level operand terms (de Bruijn variables).
///
/// UNSIGNED (`Domain::Machine`): the term Clean's own `if l < r then … else …`
/// elaborates to — `LT.lt`/`LE.le` at the carrier's own order instance, decided
/// by `instDecidable{Carrier}{Lt,Le}` / `instDecidableEq{Carrier}` — so the
/// natural island spelling matches syntactically (the 2026-07-25 Option B
/// ruling; docs/design/2026-07-25-select-encoding-ergonomics.md).
///
/// SIGNED (`Domain::Signed`, E6 widening increment 4): the natural spelling
/// CANNOT be reused — the signed carrier is `BitVec w`, and Clean's `BitVec`
/// order instances are UNSIGNED, so `instLTBitVec`-style instances would
/// silently give the program's signed `<` an unsigned meaning (at a =
/// i64::MIN, b = 0 Rust returns MIN while the unsigned reading returns 0).
/// Instead the decision is stated over the SAME sign-flip order keys the E9
/// goal builder ([`Domain::cmp`]) and the certified monitors already use:
/// `Nat.xor (BitVec.toNat w x) 2^(w-1)` maps two's-complement order to Nat
/// order bijectively, and `Nat.decLt`/`Nat.decLe`/`Nat.decEq` (axiom-free
/// prelude decision procedures) decide it. An island author writes the same
/// keys, and TRUST_E9_DEBUG prints the goal to copy them from. Equality needs
/// no sign flip (two's-complement equality is bit equality), so the Eq arm
/// compares the raw `toNat` images (injective).
fn decidable_comparison(
    d: &Domain,
    cmp: SelectCmp,
    l: Expr,
    r: Expr,
) -> Result<(Expr, Expr), String> {
    let ty = d.ty();
    let zero = Level::zero();
    let one = Level::succ(Level::zero());
    let inst_c = |s: &str| Expr::const_(Name::interned(s), vec![]);
    Ok(match d {
        Domain::Machine(w) => match cmp {
            SelectCmp::Lt => (
                Expr::apps(
                    Expr::const_(Name::interned("LT.lt"), vec![zero.clone()]),
                    [ty.clone(), inst_c(w.inst_lt_const()), l.clone(), r.clone()],
                ),
                Expr::apps(inst_c(w.inst_decidable_lt_const()), [l, r]),
            ),
            SelectCmp::Le => (
                Expr::apps(
                    Expr::const_(Name::interned("LE.le"), vec![zero.clone()]),
                    [ty.clone(), inst_c(w.inst_le_const()), l.clone(), r.clone()],
                ),
                Expr::apps(inst_c(w.inst_decidable_le_const()), [l, r]),
            ),
            SelectCmp::Eq => (
                Expr::apps(
                    Expr::const_(Name::interned("Eq"), vec![one.clone()]),
                    [ty.clone(), l.clone(), r.clone()],
                ),
                Expr::apps(inst_c(w.inst_decidable_eq_const()), [l, r]),
            ),
        },
        Domain::Signed(_) => {
            match cmp {
                SelectCmp::Lt => {
                    let (kl, kr) = (d.bitvec_order_key(l)?, d.bitvec_order_key(r)?);
                    (
                        nat_pred("Nat.lt", kl.clone(), kr.clone()),
                        Expr::apps(inst_c("Nat.decLt"), [kl, kr]),
                    )
                }
                SelectCmp::Le => {
                    let (kl, kr) = (d.bitvec_order_key(l)?, d.bitvec_order_key(r)?);
                    (
                        nat_pred("Nat.le", kl.clone(), kr.clone()),
                        Expr::apps(inst_c("Nat.decLe"), [kl, kr]),
                    )
                }
                SelectCmp::Eq => {
                    let nl = d.bitvec_to_nat(l)?;
                    let nr = d.bitvec_to_nat(r)?;
                    (
                        Expr::apps(
                            Expr::const_(Name::interned("Eq"), vec![one.clone()]),
                            [nat(), nl.clone(), nr.clone()],
                        ),
                        Expr::apps(inst_c("Nat.decEq"), [nl, nr]),
                    )
                }
            }
        }
        _ => {
            return Err(format!(
                "comparison decisions require a machine-integer or signed-integer domain, not `{}`",
                d.rust_name()
            ));
        }
    })
}

/// Mint an E6 [`Admission`] for a COMPARISON function — an n-ary function that
/// compares two of its parameters and returns the comparison itself as `Bool`,
/// i.e. `fn le(a, b) -> bool { a <= b }` (E6 widening increment 5; the
/// guard-layer decision shape). The body is `fun p0 … p_{n-1} =>
/// Decidable.decide <prop> <inst>`, with the `(prop, inst)` pair built by the
/// SAME [`decidable_comparison`] the select mint scrutinizes — so the Bool this
/// function computes is definitionally the very decision a same-comparison
/// select branches on, and the faithfulness argument is shared rather than
/// duplicated. Single machine/signed domain; `add_decl` FULL-KERNEL-CHECKS the
/// result at `d → … → Bool`.
pub fn admit_comparison_function(
    env: &mut Environment,
    kernel_const: &str,
    param_domains: &[Domain],
    cmp: SelectCmp,
    cmp_left: CmpOperand,
    cmp_right: CmpOperand,
) -> Result<Admission, String> {
    let n = param_domains.len();
    let d = param_domains.first().ok_or("comparison needs at least one parameter")?;
    if !param_domains.iter().all(|x| x == d) {
        return Err("comparison over mixed parameter domains is unsupported".into());
    }
    // At least one operand must be a PARAMETER. Two literals make the decision
    // constant-valued and leave no declared parameter type fixing their carrier
    // — the mint would be asserting a fact about a width nobody wrote.
    if !matches!(cmp_left, CmpOperand::Param(_)) && !matches!(cmp_right, CmpOperand::Param(_)) {
        return Err("a comparison mint needs at least one parameter operand".into());
    }
    // Under n binders the source parameter i is de Bruijn index n-1-i. A
    // literal takes the SAME elaboration `elab_term` gives it in a clause —
    // `Domain::zero` at 0, `Domain::numeral` above it, `negative_numeral`
    // below — because the whole value of this mint is that the clause's own
    // spelling produces a syntactically identical term.
    let operand = |o: CmpOperand| -> Result<Expr, String> {
        match o {
            CmpOperand::Param(i) => {
                if i >= n {
                    return Err(format!(
                        "comparison index {i} out of range for a {n}-parameter function"
                    ));
                }
                Ok(Expr::bvar((n - 1 - i) as u32))
            }
            CmpOperand::Const(0) => Ok(d.zero()),
            CmpOperand::Const(v) => d.numeral(v),
            CmpOperand::NegConst(magnitude) => d.negative_numeral(magnitude),
        }
    };
    let (prop, inst) = decidable_comparison(d, cmp, operand(cmp_left)?, operand(cmp_right)?)?;
    // `Decidable.decide (p : Prop) [inst : Decidable p] : Bool` — the
    // Bool-valued canonical form (`decide` is its alias in Clean's prelude).
    let body =
        Expr::apps(Expr::const_(Name::from_string("Decidable.decide"), vec![]), [prop, inst]);
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
    let lam = (0..n).fold(body, |acc, _| Expr::lam(BinderInfo::Default, d.ty(), acc));
    let arrow_ty = (0..n).fold(bool_ty, |acc, _| Expr::arrow(d.ty(), acc));
    env.add_decl(Declaration::Definition {
        name: Name::from_string(kernel_const),
        level_params: vec![],
        type_: arrow_ty,
        value: lam,
        is_reducible: true,
    })
    .map_err(|e| format!("kernel rejected the comparison defining equation: {e:?}"))?;
    // The mint's declared codomain is literally `Bool` — recording it is what
    // lets a clause type `f(a, b)` as a Bool-valued TERM (see [`Admission`]).
    Ok(Admission::reflected(kernel_const, n)
        .with_declared_signature(Some(Domain::Bool), Some(DeclaredCarriers::of_domains(param_domains, &Domain::Bool))))
}

/// The equality an [`admit_bool_cmp_function`] mints. The compiler-side twin is
/// `trust_types::e6_expr::BoolEqOp`. There is deliberately NO ordering
/// variant: `<`/`<=` over `bool` are orderings (`false < true`), and minting an
/// equality image for one would be a false import (E6 expansion review H1).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BoolCmp {
    /// `a == b` — `Decidable.decide (Eq Bool a b) (instDecidableEqBool a b)`.
    Eq,
    /// `a != b` — `Bool.not` of the `Eq` decision.
    Ne,
}

/// Mint an E6 [`Admission`] for a BOOL EQUALITY function — `fn f(a: bool, b:
/// bool) -> bool { a == b }` or `{ a != b }` (E6 admission expansion,
/// increment I1′; `docs/design-notes/2026-09-28-e6-admission-expansion.md`).
///
/// `left`/`right` are 0-based PARAMETER indices; there is no literal operand
/// (rustc simplifies `a == true` / `false != a` away before any reader sees
/// it). The body is `fun p0 … p_{n-1} => Decidable.decide (Eq.{1} Bool l r)
/// (instDecidableEqBool l r)`, wrapped in `Bool.not` for `!=`, built as kernel
/// `Expr`s directly — never printed and re-parsed (design §5 rule 3).
///
/// A NEW producer, beside the frozen [`decidable_comparison`] /
/// [`admit_comparison_function`], which refuse the `Bool` domain and stay
/// untouched: Clean-origin side B calls them directly and must not change
/// meaning (design §5 rule 1).
///
/// FAITHFULNESS: Rust `==`/`!=` on `bool` is value equality / inequality, and
/// `decide (a = b)` decided by the prelude's `instDecidableEqBool` is exactly
/// that on all four input pairs — which the E6 differential harness executes.
///
/// Fail-closed gates: every parameter's domain is `Bool` (a single domain, as
/// for every comparison mint) and both indices are in range. `add_decl` FULL-KERNEL-CHECKS the result at `Bool → … → Bool`.
pub fn admit_bool_cmp_function(
    env: &mut Environment,
    kernel_const: &str,
    param_domains: &[Domain],
    cmp: BoolCmp,
    left: usize,
    right: usize,
) -> Result<Admission, String> {
    let n = param_domains.len();
    if n == 0 {
        return Err("a bool comparison mint needs at least one parameter".into());
    }
    if !param_domains.iter().all(|d| *d == Domain::Bool) {
        return Err(
            "a bool comparison mint requires every parameter to be `bool` (a single domain)"
                .into(),
        );
    }
    let operand = |i: usize| -> Result<Expr, String> {
        if i < n {
            Ok(Expr::bvar((n - 1 - i) as u32))
        } else {
            Err(format!("bool comparison index {i} out of range for a {n}-parameter function"))
        }
    };
    let (l, r) = (operand(left)?, operand(right)?);
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
    let prop = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [bool_ty.clone(), l.clone(), r.clone()],
    );
    let inst = Expr::apps(Expr::const_(Name::from_string("instDecidableEqBool"), vec![]), [l, r]);
    let decided =
        Expr::apps(Expr::const_(Name::from_string("Decidable.decide"), vec![]), [prop, inst]);
    let body = match cmp {
        BoolCmp::Eq => decided,
        BoolCmp::Ne => Expr::app(Expr::const_(Name::from_string("Bool.not"), vec![]), decided),
    };
    let lam = (0..n).fold(body, |acc, _| Expr::lam(BinderInfo::Default, bool_ty.clone(), acc));
    let arrow_ty = (0..n).fold(bool_ty.clone(), |acc, _| Expr::arrow(bool_ty.clone(), acc));
    env.add_decl(Declaration::Definition {
        name: Name::from_string(kernel_const),
        level_params: vec![],
        type_: arrow_ty,
        value: lam,
        is_reducible: true,
    })
    .map_err(|e| format!("kernel rejected the bool comparison defining equation: {e:?}"))?;
    Ok(Admission::reflected(kernel_const, n).with_declared_signature(
        Some(Domain::Bool),
        Some(DeclaredCarriers::of_domains(param_domains, &Domain::Bool)),
    ))
}

/// The boolean connective a [`admit_bool_binary_function`] joins its two leaves
/// with. The compiler-side twin is `trust_types::admissible_body::BoolBinOp`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BoolBinOp {
    /// `&&` — minted as `Bool.and`.
    And,
    /// `||` — minted as `Bool.or`.
    Or,
}

/// Mint an E6 [`Admission`] for a BOOL-BINARY function — an n-ary function that
/// returns the CONJUNCTION or DISJUNCTION of two comparison leaves as `Bool`,
/// i.e. `fn f(x) -> bool { LO <= x && x <= HI }` (E6 widening increment 7; the
/// range-guard decision shape). The body is `fun p0 … p_{n-1} => Bool.and
/// (Decidable.decide <propA> <instA>) (Decidable.decide <propB> <instB>)` (or
/// `Bool.or` for `||`), where each `(prop, inst)` pair is built by the SAME
/// [`decidable_comparison`] and operand encoding [`admit_comparison_function`]
/// uses for a single leaf, and the connective is the SAME `Bool.and`/`Bool.or`
/// [`elab_bool_term`] emits for a clause `A && B` / `A || B`.
///
/// So the minted body is SYNTACTICALLY IDENTICAL to the term a clause
/// `result == (A && B)` elaborates on the RHS, and `Eq.refl` closes the
/// discharge with nothing clever — exactly the single-comparison property, one
/// `Bool.and`/`Bool.or` layer up. Single machine/signed domain (all parameters
/// share one carrier); `add_decl` FULL-KERNEL-CHECKS the result at
/// `d → … → Bool`.
///
/// FAITHFULNESS: Rust `A && B` on two PURE, PANIC-FREE `bool` subexpressions
/// equals the non-short-circuit `Bool.and` of their values (short-circuit only
/// changes WHETHER `B` is evaluated, never the result, and `B` has no effect);
/// likewise `A || B` = `Bool.or A B`. Each leaf is a comparison the leaf mint
/// already admits exactly, so the composition is exact on every input.
#[allow(clippy::too_many_arguments)]
pub fn admit_bool_binary_function(
    env: &mut Environment,
    kernel_const: &str,
    param_domains: &[Domain],
    op: BoolBinOp,
    left_cmp: SelectCmp,
    left_l: CmpOperand,
    left_r: CmpOperand,
    right_cmp: SelectCmp,
    right_l: CmpOperand,
    right_r: CmpOperand,
) -> Result<Admission, String> {
    let n = param_domains.len();
    let d = param_domains.first().ok_or("bool-binary needs at least one parameter")?;
    if !param_domains.iter().all(|x| x == d) {
        return Err("bool-binary over mixed parameter domains is unsupported".into());
    }
    // Each leaf needs ≥1 parameter operand, exactly as the single-comparison
    // mint does — a two-constant leaf has no declared parameter fixing its
    // carrier, so the mint would assert a fact about a width nobody wrote.
    for (l, r) in [(left_l, left_r), (right_l, right_r)] {
        if !matches!(l, CmpOperand::Param(_)) && !matches!(r, CmpOperand::Param(_)) {
            return Err("each comparison leaf of a bool-binary needs a parameter operand".into());
        }
    }
    // Under n binders the source parameter i is de Bruijn index n-1-i; a
    // literal takes the SAME `elab_term` elaboration a clause gives it. This is
    // byte-for-byte the encoding [`admit_comparison_function`] uses.
    let operand = |o: CmpOperand| -> Result<Expr, String> {
        match o {
            CmpOperand::Param(i) => {
                if i >= n {
                    return Err(format!(
                        "bool-binary index {i} out of range for a {n}-parameter function"
                    ));
                }
                Ok(Expr::bvar((n - 1 - i) as u32))
            }
            CmpOperand::Const(0) => Ok(d.zero()),
            CmpOperand::Const(v) => d.numeral(v),
            CmpOperand::NegConst(magnitude) => d.negative_numeral(magnitude),
        }
    };
    // One leaf → `Decidable.decide <prop> <inst>`, the same Bool-valued form the
    // single-comparison mint emits and [`elab_bool_term`] emits for a clause
    // comparison.
    let decide = |cmp: SelectCmp, l: CmpOperand, r: CmpOperand| -> Result<Expr, String> {
        let (prop, inst) = decidable_comparison(d, cmp, operand(l)?, operand(r)?)?;
        Ok(Expr::apps(Expr::const_(Name::from_string("Decidable.decide"), vec![]), [prop, inst]))
    };
    let lhs = decide(left_cmp, left_l, left_r)?;
    let rhs = decide(right_cmp, right_l, right_r)?;
    // `Bool.and`/`Bool.or` applied to the two decided leaves — the exact
    // connective and spelling `elab_bool_term` produces for `A && B` / `A || B`.
    let connective = match op {
        BoolBinOp::And => "Bool.and",
        BoolBinOp::Or => "Bool.or",
    };
    let body = Expr::apps(Expr::const_(Name::from_string(connective), vec![]), [lhs, rhs]);
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
    let lam = (0..n).fold(body, |acc, _| Expr::lam(BinderInfo::Default, d.ty(), acc));
    let arrow_ty = (0..n).fold(bool_ty, |acc, _| Expr::arrow(d.ty(), acc));
    env.add_decl(Declaration::Definition {
        name: Name::from_string(kernel_const),
        level_params: vec![],
        type_: arrow_ty,
        value: lam,
        is_reducible: true,
    })
    .map_err(|e| format!("kernel rejected the bool-binary defining equation: {e:?}"))?;
    Ok(Admission::reflected(kernel_const, n)
        .with_declared_signature(Some(Domain::Bool), Some(DeclaredCarriers::of_domains(param_domains, &Domain::Bool))))
}

/// **W6 (Rust-calls-Clean)** — the boolean-VALUE operation an
/// [`admit_bool_value_function`] mints: a negation or a strict connective over
/// `Bool` PARAMETERS, returned as `Bool`. The compiler-side twin is
/// `trust_types::admissible_body::BoolValueKind`.
///
/// Distinct from [`BoolBinOp`], which joins two COMPARISON leaves for the
/// range-guard idiom (`LO <= x && x <= HI`): this one joins bare boolean
/// parameters (`fn conj(a: bool, b: bool) -> bool { a && b }`), the shape a
/// Clean `def f (a b : Bool) : Bool := a && b` takes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BoolValueKind {
    /// `not b` — minted as `Bool.not (param)`.
    Not(usize),
    /// `a && b` — minted as `Bool.and (left) (right)`.
    And(usize, usize),
    /// `a || b` — minted as `Bool.or (left) (right)`.
    Or(usize, usize),
}

/// Mint an E6-style [`Admission`] for a BOOLEAN-VALUE function — a negation or a
/// strict conjunction/disjunction of `Bool` PARAMETERS returned as `Bool`
/// (`def f (a b : Bool) : Bool := a && b`, whose kernel body is `and a b`; W6,
/// Rust calls a Clean boolean connective). The body is `fun p0 … p_{n-1} =>
/// Bool.not (p)` / `Bool.and (l) (r)` / `Bool.or (l) (r)`, the SAME `Bool.not`/
/// `Bool.and`/`Bool.or` spelling [`elab_bool_term`] emits for a clause `!a` /
/// `a && b` / `a || b`.
///
/// FAITHFULNESS: the island's `&&`/`||`/`not` on `Bool` are the STRICT total
/// functions `and`/`or`/`Bool.not`, which are definitionally equal to
/// `Bool.and`/`Bool.or`/`Bool.not` (measured 2026-09-13), and the emitted MIR
/// (`BitAnd`/`BitOr`/`UnaryOp(Not)` on `bool`) computes exactly those on every
/// input — short-circuit is observationally identical when the operands are
/// pure `bool` parameters with no effect. Every parameter carries `Bool`;
/// `add_decl` FULL-KERNEL-CHECKS the result at `Bool → … → Bool`.
///
/// This is NOT a frozen E6 producer — it is authored for the W6 CALL lane — so
/// its row carries its own `docs/TCB.md` line (it mints a direct kernel
/// application rather than riding frozen-R's elaboration pedigree).
pub fn admit_bool_value_function(
    env: &mut Environment,
    kernel_const: &str,
    param_domains: &[Domain],
    op: BoolValueKind,
) -> Result<Admission, String> {
    let n = param_domains.len();
    if !param_domains.iter().all(|d| *d == Domain::Bool) {
        return Err("a boolean-value function's parameters must all be `Bool`".into());
    }
    let bvar = |i: usize| -> Result<Expr, String> {
        if i >= n {
            return Err(format!("bool-value index {i} out of range for a {n}-parameter function"));
        }
        // Under n binders the source parameter i is de Bruijn index n-1-i.
        Ok(Expr::bvar(de_bruijn_index(n, i, 0)?))
    };
    let body = match op {
        BoolValueKind::Not(p) => {
            Expr::apps(Expr::const_(Name::from_string("Bool.not"), vec![]), [bvar(p)?])
        }
        BoolValueKind::And(l, r) => {
            Expr::apps(Expr::const_(Name::from_string("Bool.and"), vec![]), [bvar(l)?, bvar(r)?])
        }
        BoolValueKind::Or(l, r) => {
            Expr::apps(Expr::const_(Name::from_string("Bool.or"), vec![]), [bvar(l)?, bvar(r)?])
        }
    };
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
    let lam = (0..n).fold(body, |acc, _| Expr::lam(BinderInfo::Default, bool_ty.clone(), acc));
    let arrow_ty = (0..n).fold(bool_ty.clone(), |acc, _| Expr::arrow(bool_ty.clone(), acc));
    env.add_decl(Declaration::Definition {
        name: Name::from_string(kernel_const),
        level_params: vec![],
        type_: arrow_ty,
        value: lam,
        is_reducible: true,
    })
    .map_err(|e| format!("kernel rejected the boolean-value defining equation: {e:?}"))?;
    Ok(Admission::reflected(kernel_const, n).with_declared_signature(
        Some(Domain::Bool),
        Some(DeclaredCarriers::of_domains(param_domains, &Domain::Bool)),
    ))
}

/// The checked operation an [`admit_checked_arithmetic_function`] mints. The
/// compiler-side twin is `trust_types::admissible_body::CheckedArithOp`; this
/// crate carries its own copy for the same dependency-boundary reason as
/// [`CmpOperand`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CheckedArithOp {
    /// `checked_add` — minted over `Int.add`.
    Add,
    /// `checked_sub` — minted over `Int.sub`.
    Sub,
    /// `checked_mul` — minted over `Int.mul`.
    Mul,
}

impl CheckedArithOp {
    const fn int_op(self) -> &'static str {
        match self {
            Self::Add => "Int.add",
            Self::Sub => "Int.sub",
            Self::Mul => "Int.mul",
        }
    }

    const fn model_suffix(self) -> &'static str {
        match self {
            Self::Add => "Add",
            Self::Sub => "Sub",
            Self::Mul => "Mul",
        }
    }
}

/// The reserved name of one seeded checked-arithmetic model definition. Flat
/// `trust_checked_*` identifiers: they cannot collide with the kernel-import
/// namespace (`trust_import_*`), and an island that (perversely) declares one
/// makes the seeding fail CLOSED via the structural-identity check in
/// [`seed_decl`] rather than silently reusing a foreign body.
fn checked_model_name(stem: &str, bits: u32) -> String {
    format!("trust_checked_{stem}{bits}")
}

/// Add one seeded model definition, idempotently and fail-closed: a fresh name
/// is `add_decl`ed (FULL kernel check, `is_reducible` so definitional equality
/// may unfold it); an existing SAME-BODY definition is accepted (the seeding
/// ran before, e.g. for a sibling function); an existing name with ANY OTHER
/// body or kind is a hard error — the mint must never build on a homonym it
/// did not seed.
fn seed_decl(env: &mut Environment, name: &str, type_: Expr, value: Expr) -> Result<(), String> {
    let kernel_name = Name::from_string(name);
    if let Some(existing) = env.get_const(&kernel_name) {
        if existing.type_ == type_ && existing.value.as_ref() == Some(&value) {
            return Ok(());
        }
        return Err(format!(
            "seeded checked-arithmetic model `{name}` already exists with a DIFFERENT \
             definition; refusing to mint on top of a foreign homonym"
        ));
    }
    env.add_decl(Declaration::Definition {
        name: kernel_name,
        level_params: vec![],
        type_,
        value,
        is_reducible: true,
    })
    .map_err(|e| format!("kernel rejected seeded checked-arithmetic model `{name}`: {e:?}"))
}

/// Seed the width-`N` checked-arithmetic kernel model into `env`, ONCE — the
/// NORMATIVE AUTHORED SPELLINGS of the veripb client kernel
/// (`veripb_kernel.lean` §"Overflow-checked signed arithmetic", the plan of
/// record), so a client island's own `checkedOpN` is DELTA-DEFEQ to the seeded
/// twin: every definition below has byte-level the term structure the island
/// elaborator produces for the authored Lean text (measured 2026-08-25 —
/// `Bool.casesOn.{1}` with an anonymous motive, scrutinee, FALSE arm, TRUE
/// arm), so lazy-delta `is_def_eq` unfolds the two chains in lock-step and
/// closes on the shared `Nat`/`Int`/`BitVec`/`Option` prelude spine.
///
/// The load-bearing spelling decisions, verbatim from the client kernel's
/// AUTHORING CONSTRAINT note:
///   * `toIntN` is the SIGN-CASE MATCH on the order key — `Nat.ble pivot
///     (keyN v)`, `Int.ofNat (keyN v - pivot)` / `Int.negSucc (maxpos - keyN
///     v)` — deliberately NOT `Int.sub` of `ofNat` literals, whose unary
///     unfolding costs ~2^63 iota steps the moment a whnf touches it. The
///     match spelling whnf-sticks cheaply at the `Nat.ble` scrutinee.
///   * `fitsIN` has exactly the `fitsI64` guard shape (nested `Int.ble`
///     match); `ofIntN` re-embeds sign-branched (`Int.toNat x` when
///     `0 <= x`, else `Int.toNat (x + 2^N)`) so every `ofNat` operand stays
///     below the numeral reducers' u128 read cap.
///   * the order key is the SAME `Nat.xor (BitVec.toNat v) 2^(N-1)` the
///     elaborator already stakes signed-comparison soundness on
///     ([`Domain::bitvec_order_key`]) — no new trusted primitive.
fn seed_checked_model(env: &mut Environment, width: MachineSIntWidth) -> Result<(), String> {
    let bits = width.bits();
    let signed = Domain::Signed(width);
    let bv_ty = signed.ty();
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
    let option_bv_ty = Domain::OptionSigned(width).ty();
    let one = Level::succ(Level::zero());
    let c = |s: &str| Expr::const_(Name::from_string(s), vec![]);
    let pivot = 1u128 << (bits - 1); // 2^(N-1)
    let maxpos = pivot - 1; // 2^(N-1) - 1
    // 2^N — the re-embed offset. Exceeds `u128` at N = 128, so it is built
    // from limbs there (the island's parser produces the same multi-limb
    // literal for the authored decimal).
    let embed = if bits < 128 {
        kernel_nat_lit(1u128 << bits)
    } else {
        Expr::bignat_lit(clean_kernel::BigNat::from_limbs(vec![0, 0, 1]))
    };

    // Bool.casesOn.{1} <motive> <scrutinee> <false-arm> <true-arm> — the term
    // the island elaborator produces for a two-arm Bool `match` (minors in
    // CONSTRUCTOR order: `false` first).
    let bool_cases = |target_ty: Expr, scrutinee: Expr, false_arm: Expr, true_arm: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Bool.casesOn"), vec![one.clone()]),
            [
                Expr::lam(BinderInfo::Default, bool_ty.clone(), target_ty),
                scrutinee,
                false_arm,
                true_arm,
            ],
        )
    };

    // key: fun (v : BitVec N) => Nat.xor (BitVec.toNat N v) 2^(N-1) — exactly
    // the elaborator's own signed order key.
    let key_name = checked_model_name("key", bits);
    let key_body = signed.bitvec_order_key(Expr::bvar(0))?;
    seed_decl(
        env,
        &key_name,
        Expr::arrow(bv_ty.clone(), nat()),
        Expr::lam(BinderInfo::Default, bv_ty.clone(), key_body),
    )?;
    let key_of = |v: Expr| Expr::app(c(&key_name), v);

    // toInt: the sign-case match on the key (see the doc above).
    let to_int_name = checked_model_name("toInt", bits);
    let to_int_body = bool_cases(
        int_ty.clone(),
        Expr::apps(c("Nat.ble"), [kernel_nat_lit(pivot), key_of(Expr::bvar(0))]),
        Expr::app(
            c("Int.negSucc"),
            Expr::apps(c("Nat.sub"), [kernel_nat_lit(maxpos), key_of(Expr::bvar(0))]),
        ),
        Expr::app(
            c("Int.ofNat"),
            Expr::apps(c("Nat.sub"), [key_of(Expr::bvar(0)), kernel_nat_lit(pivot)]),
        ),
    );
    seed_decl(
        env,
        &to_int_name,
        Expr::arrow(bv_ty.clone(), int_ty.clone()),
        Expr::lam(BinderInfo::Default, bv_ty.clone(), to_int_body),
    )?;
    let to_int_of = |v: Expr| Expr::app(c(&to_int_name), v);

    // iNMax / iNMin — the guard bounds, at `Int`.
    let max_name = checked_model_name("iMax", bits);
    seed_decl(
        env,
        &max_name,
        int_ty.clone(),
        Expr::app(c("Int.ofNat"), kernel_nat_lit(maxpos)),
    )?;
    let min_name = checked_model_name("iMin", bits);
    seed_decl(
        env,
        &min_name,
        int_ty.clone(),
        Expr::app(c("Int.neg"), Expr::app(c("Int.ofNat"), kernel_nat_lit(pivot))),
    )?;

    // fits: fun (x : Int) => match Int.ble iNMin x with
    //       | true => Int.ble x iNMax | false => false — the `fitsI64` shape.
    let fits_name = checked_model_name("fitsI", bits);
    let fits_body = bool_cases(
        bool_ty.clone(),
        Expr::apps(c("Int.ble"), [c(&min_name), Expr::bvar(0)]),
        // The island elaborator spells the authored `| false => false` VALUE
        // as the prelude's root-level `false` constant (measured 2026-08-25);
        // matching it exactly keeps the false arms structurally identical
        // with no reliance on that alias being reducible.
        c("false"),
        Expr::apps(c("Int.ble"), [Expr::bvar(0), c(&max_name)]),
    );
    seed_decl(
        env,
        &fits_name,
        Expr::arrow(int_ty.clone(), bool_ty.clone()),
        Expr::lam(BinderInfo::Default, int_ty.clone(), fits_body),
    )?;

    // ofInt: SIGN-BRANCHED, mirroring the authored client spelling —
    //   fun (x : Int) => match Int.ble (Int.ofNat 0) x with
    //     | true  => BitVec.ofNat N (Int.toNat x)
    //     | false => BitVec.ofNat N (Int.toNat (Int.add x (Int.ofNat 2^N))).
    // The branch is load-bearing at N = 128: an unconditional `x + 2^N` shift
    // puts every non-negative fitting result at or above 2^128, past the
    // numeral reducers' u128 read cap, parking the re-embed of exactly the
    // common case in closed-term evaluation. Extensionally the two spellings
    // agree at every Int (non-negative: both reduce mod 2^N).
    let of_int_name = checked_model_name("ofInt", bits);
    let of_int_direct = signed.bitvec_of_nat(Expr::app(c("Int.toNat"), Expr::bvar(0)))?;
    let of_int_shifted = signed.bitvec_of_nat(Expr::app(
        c("Int.toNat"),
        Expr::apps(c("Int.add"), [Expr::bvar(0), Expr::app(c("Int.ofNat"), embed)]),
    ))?;
    let of_int_body = bool_cases(
        bv_ty.clone(),
        Expr::apps(
            c("Int.ble"),
            [Expr::app(c("Int.ofNat"), kernel_nat_lit(0)), Expr::bvar(0)],
        ),
        of_int_shifted,
        of_int_direct,
    );
    seed_decl(
        env,
        &of_int_name,
        Expr::arrow(int_ty.clone(), bv_ty.clone()),
        Expr::lam(BinderInfo::Default, int_ty.clone(), of_int_body),
    )?;

    // checkedOp (×3): fun a b => match fitsIN (Int.op (toIntN a) (toIntN b))
    //   with | true => some (ofIntN (Int.op …)) | false => none.
    for op in [CheckedArithOp::Add, CheckedArithOp::Sub, CheckedArithOp::Mul] {
        let exact = || {
            Expr::apps(
                c(op.int_op()),
                [to_int_of(Expr::bvar(1)), to_int_of(Expr::bvar(0))],
            )
        };
        let body = bool_cases(
            option_bv_ty.clone(),
            Expr::app(c(&fits_name), exact()),
            Expr::app(
                Expr::const_(Name::from_string("Option.none"), vec![Level::zero()]),
                bv_ty.clone(),
            ),
            Expr::apps(
                Expr::const_(Name::from_string("Option.some"), vec![Level::zero()]),
                [bv_ty.clone(), Expr::app(c(&of_int_name), exact())],
            ),
        );
        seed_decl(
            env,
            &checked_model_name(&format!("checked{}", op.model_suffix()), bits),
            Expr::arrow(bv_ty.clone(), Expr::arrow(bv_ty.clone(), option_bv_ty.clone())),
            Expr::lam(
                BinderInfo::Default,
                bv_ty.clone(),
                Expr::lam(BinderInfo::Default, bv_ty.clone(), body),
            ),
        )?;
    }
    Ok(())
}

/// Seed the width-`N` SIGNED LIFT MODEL into `env` — the public, idempotent
/// entry to exactly the definitions [`seed_checked_model`] already mints.
///
/// The nat-lift table's `iN → Int` row (§3.1 of the nat-lift design) emits
/// `trust_checked_toInt{N}` by NAME, and the elaborator holds no environment,
/// so whoever builds a lifted goal must make sure the constant the name
/// resolves to is the one this tree defines. That is this function: it is the
/// SAME `seed_decl` discipline (a fresh name is full-kernel-checked; an
/// existing SAME-BODY definition is accepted; an existing homonym with any
/// other body is a hard error), so an island that declares its own
/// `trust_checked_toInt64` makes the seeding — and therefore the clause —
/// fail closed instead of capturing the lift.
///
/// It seeds the whole width-`N` model, not the `toInt` constant alone,
/// deliberately: the model's definitions are mutually referential
/// (`toIntN` is defined through `keyN`), and seeding a subset would leave the
/// environment in a state `seed_decl`'s same-body check could not later
/// complete.
pub fn seed_signed_lift_model(
    env: &mut Environment,
    width: MachineSIntWidth,
) -> Result<(), String> {
    seed_checked_model(env, width)
}

/// The kernel constant name of the width-`N` signed lift (`iN → Int`), for a
/// caller that must reserve or recognize it. Diagnostics and tests only: the
/// lift table builds the term itself.
#[must_use]
pub fn signed_lift_const_name(width: MachineSIntWidth) -> String {
    width.signed_lift_const().to_string()
}

/// Mint an E6 [`Admission`] for an overflow-CHECKED SIGNED arithmetic function
/// — `fn cadd(a: iN, b: iN) -> Option<iN> { a.checked_add(b) }` (recognized as
/// `trust_types::admissible_body::AdmissibleBody::CheckedArithmetic`). The
/// width-`N` kernel model of [`seed_checked_model`] is seeded ONCE, and the
/// minted defining equation is just the applied seeded constant:
/// `fun p0 … p_{n-1} => trust_checked_checkedOpN <left> <right>` at type
/// `BitVec N → … → Option (BitVec N)`, FULL-KERNEL-CHECKED by `add_decl`.
///
/// SOUNDNESS: `add_decl` guarantees well-typedness, not fidelity — fidelity
/// rests on (a) the recognizer's exactness (the body IS the checked op on
/// exactly these operands) and (b) the seeded model being the faithful total
/// model of `iN::checked_op` (exact `Int` result + `fits` guard + wrapping
/// re-embed — no false `Some`, no false `None`, `MIN*-1`-class edges included
/// by unboundedness). The §5.7 NEG probes pin that a swapped `some`/`none` or
/// an `add`↔`sub` swap in the seeded model is CAUGHT by definitional
/// comparison against the island's authored spelling, not silently green.
pub fn admit_checked_arithmetic_function(
    env: &mut Environment,
    kernel_const: &str,
    param_domains: &[Domain],
    op: CheckedArithOp,
    width: MachineSIntWidth,
    left: CmpOperand,
    right: CmpOperand,
) -> Result<Admission, String> {
    let n = param_domains.len();
    let d = Domain::Signed(width);
    if n == 0 {
        return Err("a checked-arithmetic mint needs at least one parameter".into());
    }
    if !param_domains.iter().all(|x| *x == d) {
        return Err(format!(
            "checked arithmetic requires every parameter at the operand carrier `{}`",
            d.rust_name()
        ));
    }
    if !matches!(left, CmpOperand::Param(_)) && !matches!(right, CmpOperand::Param(_)) {
        return Err("a checked-arithmetic mint needs at least one parameter operand".into());
    }
    // Operands take the SAME elaboration a clause literal gets (`Domain::zero`
    // at 0, `numeral` above — range-checked at the signed carrier). A negative
    // literal has no recognizer spelling and fails closed here too.
    let operand = |o: CmpOperand| -> Result<Expr, String> {
        match o {
            CmpOperand::Param(i) => {
                if i >= n {
                    return Err(format!(
                        "checked-arithmetic operand index {i} out of range for a \
                         {n}-parameter function"
                    ));
                }
                Ok(Expr::bvar((n - 1 - i) as u32))
            }
            CmpOperand::Const(0) => Ok(d.zero()),
            CmpOperand::Const(v) => d.numeral(v),
            CmpOperand::NegConst(_) => Err(
                "a negative literal operand has no checked-arithmetic recognizer spelling \
                 and fails closed"
                    .into(),
            ),
        }
    };
    let (l, r) = (operand(left)?, operand(right)?);
    seed_checked_model(env, width)?;
    let checked_const =
        checked_model_name(&format!("checked{}", op.model_suffix()), width.bits());
    let body = Expr::apps(Expr::const_(Name::from_string(&checked_const), vec![]), [l, r]);
    let ret_ty = Domain::OptionSigned(width).ty();
    let lam = (0..n).fold(body, |acc, _| Expr::lam(BinderInfo::Default, d.ty(), acc));
    let arrow_ty = (0..n).fold(ret_ty, |acc, _| Expr::arrow(d.ty(), acc));
    env.add_decl(Declaration::Definition {
        name: Name::from_string(kernel_const),
        level_params: vec![],
        type_: arrow_ty,
        value: lam,
        is_reducible: true,
    })
    .map_err(|e| format!("kernel rejected the checked-arithmetic defining equation: {e:?}"))?;
    Ok(Admission::reflected(kernel_const, n)
        .with_declared_signature(Some(Domain::OptionSigned(width)), Some(DeclaredCarriers::of_domains(
            param_domains,
            &Domain::OptionSigned(width),
        ))))
}

/// The reserved name of the seeded TRUNCATION model — the exact kernel term
/// for rustc's `IntToInt` narrowing cast. Same `trust_checked_*` namespace (and
/// therefore the same [`seed_decl`] homonym guard) as the checked-arithmetic
/// model it composes with.
fn trunc_model_name(from_bits: u32, to_bits: u32) -> String {
    format!("trust_checked_trunc{from_bits}to{to_bits}")
}

/// The reserved name of the seeded GUARDED-NARROW model.
fn narrow_model_name(from_bits: u32, to_bits: u32) -> String {
    format!("trust_checked_narrowI{from_bits}toI{to_bits}")
}

/// The reserved name of the seeded SIGN-EXTENSION model — the exact kernel
/// term for rustc's `IntToInt` signed WIDENING cast. Same `trust_checked_*`
/// namespace, and therefore the same [`seed_decl`] homonym guard, as the
/// truncation model it mirrors.
fn sext_model_name(from_bits: u32, to_bits: u32) -> String {
    format!("trust_checked_sextI{from_bits}toI{to_bits}")
}

/// Seed the SIGN-EXTENSION kernel model into `env`, ONCE:
///
/// ```lean
/// def sextI64toI128 (v : BitVec 64) : BitVec 128 :=
///     ofInt128 (toInt64 v)
/// ```
///
/// It introduces NO new primitive and NO new literal. Both halves already
/// exist as the checked lane's exact-`Int` bridge: [`seed_checked_model`] at
/// the SOURCE width supplies `toInt`, and at the TARGET width supplies
/// `ofInt`, in the client kernel's normative authored spellings. So a client
/// island composing its own authored `toInt64`/`ofInt128` the same way is
/// DELTA-DEFEQ to this twin, and — like `trunc` — as an OPEN term it parks
/// cheaply (`toInt64` sticks at its `Nat.ble` scrutinee, `ofInt128` at its
/// `Int.ble` scrutinee applied to that stuck term), which is exactly what
/// delta-defeq wants: both sides of a citation goal carry the identical stuck
/// spelling.
///
/// FAITHFULNESS, unconditionally, on all `2^FROM` inputs. rustc's `IntToInt`
/// cast from `iFROM` to a strictly wider `iTO` is two's-complement SIGN
/// EXTENSION: it preserves the mathematical value. The model says exactly
/// that, in two exact steps:
///   * `toIntFROM v` is the exact signed value of `v`, in
///     `[-2^(FROM-1), 2^(FROM-1) - 1]` — the same bridge the checked lane
///     already stakes its overflow verdicts on;
///   * `ofIntTO x` re-embeds an `Int` as its two's-complement `BitVec TO`
///     pattern, and it is EXACT for every `x` in that range because the range
///     is strictly inside `[-2^(TO-1), 2^(TO-1))` whenever `FROM < TO` — the
///     non-negative branch takes `BitVec.ofNat TO (Int.toNat x)` with
///     `x < 2^(FROM-1) < 2^TO`, and the negative branch takes
///     `BitVec.ofNat TO (Int.toNat (x + 2^TO))` with
///     `2^TO - 2^(FROM-1) <= x + 2^TO < 2^TO`. Neither `ofNat` wraps.
/// So `ofIntTO (toIntFROM v)` is the unique `BitVec TO` with the same signed
/// value as `v` — the sign extension — with no dependence on any guard and no
/// input excluded. In particular it is NOT zero extension: at `v = -1`
/// (`0xFFFF…F` at 64 bits) it yields the all-ones `BitVec 128`, where
/// `BitVec.ofNat 128 (BitVec.toNat v)` would yield `2^64 - 1`.
///
/// `FROM < TO` is asserted here rather than assumed: at `FROM >= TO` the
/// re-embed is a wrapping truncation and this name would be a lie, so the
/// seeding fails closed instead.
///
/// SYNC DISCIPLINE: this definition joins the checked and narrow models'
/// synchronized copies — the client kernel text, this seeder, the
/// trust-certify def-eq oracle fixture, and the probe islands. Change all of
/// them together.
fn seed_sext_model(
    env: &mut Environment,
    from: MachineSIntWidth,
    to: MachineSIntWidth,
) -> Result<(), String> {
    let (from_bits, to_bits) = (from.bits(), to.bits());
    if from_bits >= to_bits {
        return Err(format!(
            "the sign-extension model requires a strictly WIDER target: \
             `{}` -> `{}` is not a widening",
            Domain::Signed(from).rust_name(),
            Domain::Signed(to).rust_name()
        ));
    }
    seed_checked_model(env, from)?;
    seed_checked_model(env, to)?;
    let (narrow_ty, wide_ty) = (Domain::Signed(from).ty(), Domain::Signed(to).ty());
    let c = |s: &str| Expr::const_(Name::from_string(s), vec![]);
    let body = Expr::app(
        c(&checked_model_name("ofInt", to_bits)),
        Expr::app(c(&checked_model_name("toInt", from_bits)), Expr::bvar(0)),
    );
    seed_decl(
        env,
        &sext_model_name(from_bits, to_bits),
        Expr::arrow(narrow_ty.clone(), wide_ty),
        Expr::lam(BinderInfo::Default, narrow_ty, body),
    )
}

/// Mint an E6 [`Admission`] for a WIDENING-CAST EQUALITY function — the body
/// of `veripb_core_proved::guard::eq_ok`, recognized as
/// `trust_types::admissible_body::AdmissibleBody::WidenedEq`:
/// `fn eq_ok(machine: i64, truth: i128) -> bool { Wide::from(machine) == truth }`.
///
/// The minted defining equation is
/// `fun p0 … p_{n-1} => Decidable.decide <prop> <inst>`, where `(prop, inst)`
/// is built by the SAME [`decidable_comparison`] every other bool-decision
/// mint uses — at the WIDE domain, where both sides now live — with the narrow
/// operand wrapped in the seeded [`seed_sext_model`] constant:
///
/// ```text
/// fun (p0 : BitVec 64) (p1 : BitVec 128) =>
///   Decidable.decide
///     (Eq Nat (BitVec.toNat 128 (trust_checked_sextI64toI128 p0))
///             (BitVec.toNat 128 p1))
///     (Nat.decEq (BitVec.toNat 128 (trust_checked_sextI64toI128 p0))
///                (BitVec.toNat 128 p1))
/// ```
///
/// The type is the MIXED arrow `BitVec 64 → BitVec 128 → Bool`, so — unlike
/// [`admit_comparison_function`] — the parameter domains are deliberately NOT
/// required to agree; each binder takes its own carrier, and the lambda is
/// folded in REVERSE parameter order so the de Bruijn index `n - 1 - i` names
/// the intended parameter even though the carriers differ.
///
/// MONOMORPHIC this increment: only `(i64 → i128)`, signed to signed. Other
/// pairs PARK — their MIR is unmeasured, and a narrowing pair would need the
/// truncation model, not this one.
///
/// SOUNDNESS: `add_decl` guarantees well-typedness, not fidelity. Fidelity
/// rests on (a) the recognizer's exactness — the body IS an `Eq` between a
/// signed widening cast of exactly this parameter and exactly that one — and
/// (b) the seeded model being the exact TOTAL model of that cast on every
/// input, negatives included (see [`seed_sext_model`]). The equality half
/// claims nothing new: it is the `Domain::Signed` `Eq` spelling the
/// comparison lane already mints, evaluated at the wide carrier.
#[allow(clippy::too_many_arguments)]
pub fn admit_widened_eq_function(
    env: &mut Environment,
    kernel_const: &str,
    param_domains: &[Domain],
    from: MachineSIntWidth,
    to: MachineSIntWidth,
    narrow_param: usize,
    wide_param: usize,
    cast_on_left: bool,
) -> Result<Admission, String> {
    let n = param_domains.len();
    if narrow_param >= n || wide_param >= n {
        return Err(format!(
            "widened-equality parameter indices ({narrow_param}, {wide_param}) are out of \
             range for a {n}-parameter function"
        ));
    }
    if narrow_param == wide_param {
        return Err(
            "a widened equality compares TWO distinct parameters; the same index on both \
             sides has no mixed-width reading and fails closed"
                .into(),
        );
    }
    if from != MachineSIntWidth::I64 || to != MachineSIntWidth::I128 {
        return Err(format!(
            "the widening-cast comparison lane is monomorphic this increment: only \
             `{}` -> `{}` is admitted, not `{}` -> `{}`",
            Domain::Signed(MachineSIntWidth::I64).rust_name(),
            Domain::Signed(MachineSIntWidth::I128).rust_name(),
            Domain::Signed(from).rust_name(),
            Domain::Signed(to).rust_name()
        ));
    }
    let (narrow_d, wide_d) = (Domain::Signed(from), Domain::Signed(to));
    if param_domains[narrow_param] != narrow_d {
        return Err(format!(
            "the widened parameter must live at the source carrier `{}`, not `{}`",
            narrow_d.rust_name(),
            param_domains[narrow_param].rust_name()
        ));
    }
    if param_domains[wide_param] != wide_d {
        return Err(format!(
            "the compared parameter must live at the target carrier `{}`, not `{}`",
            wide_d.rust_name(),
            param_domains[wide_param].rust_name()
        ));
    }
    seed_sext_model(env, from, to)?;
    // Under n binders the source parameter i is de Bruijn index n-1-i.
    let widened = Expr::app(
        Expr::const_(Name::from_string(&sext_model_name(from.bits(), to.bits())), vec![]),
        Expr::bvar((n - 1 - narrow_param) as u32),
    );
    let other = Expr::bvar((n - 1 - wide_param) as u32);
    // The minted `Eq` is spelled over `BitVec.toNat` of each side and is not
    // syntactically symmetric, so the SOURCE's operand order is reproduced.
    let (l, r) = if cast_on_left { (widened, other) } else { (other, widened) };
    let (prop, inst) = decidable_comparison(&wide_d, SelectCmp::Eq, l, r)?;
    let body =
        Expr::apps(Expr::const_(Name::from_string("Decidable.decide"), vec![]), [prop, inst]);
    // MIXED carriers: fold each binder at its OWN domain, in reverse parameter
    // order, so the outermost binder is `p0`.
    let lam = param_domains
        .iter()
        .rev()
        .fold(body, |acc, d| Expr::lam(BinderInfo::Default, d.ty(), acc));
    let arrow_ty = param_domains
        .iter()
        .rev()
        .fold(Expr::const_(Name::from_string("Bool"), vec![]), |acc, d| {
            Expr::arrow(d.ty(), acc)
        });
    env.add_decl(Declaration::Definition {
        name: Name::from_string(kernel_const),
        level_params: vec![],
        type_: arrow_ty,
        value: lam,
        is_reducible: true,
    })
    .map_err(|e| format!("kernel rejected the widened-equality defining equation: {e:?}"))?;
    Ok(Admission::reflected(kernel_const, n)
        .with_declared_signature(Some(Domain::Bool), Some(DeclaredCarriers::of_domains(param_domains, &Domain::Bool))))
}

/// Seed the guarded-NARROWING kernel model into `env`, ONCE — again the
/// NORMATIVE AUTHORED SPELLING of the veripb client kernel, so a client
/// island's own `narrowWide` is DELTA-DEFEQ to the seeded twin:
///
/// ```lean
/// def trunc64 (v : BitVec 128) : BitVec 64 :=
///     BitVec.ofNat 64 (BitVec.toNat v)
/// def narrowWide (x : BitVec 128) : Option (BitVec 64) :=
///     match fitsI64 (toInt128 x) with
///     | true  => some (trunc64 x)
///     | false => none
/// ```
///
/// Everything but those two definitions already exists: the guard reads the
/// TARGET width's `fitsI` over the SOURCE width's exact-`Int` bridge, so both
/// widths' [`seed_checked_model`]s are seeded and supply `toInt`, `fitsI` and
/// the bounds unchanged. `trunc` introduces NO new primitive — it is
/// `BitVec.ofNat` of `BitVec.toNat`, and as an OPEN term it parks (the `toNat`
/// reducer is peel-structural), which is exactly what delta-defeq wants: both
/// sides of a citation goal carry the identical stuck spelling.
///
/// FAITHFULNESS, unconditionally. rustc's `IntToInt` cast from `iW` to `iN` is
/// two's-complement TRUNCATION — the low `N` bits — which is `toNat mod 2^N` =
/// `BitVec.ofNat N (BitVec.toNat v)`. The model is therefore exact on EVERY
/// input, including inputs the guard rejects; no soundness rests on the guard
/// making the cast benign. The guard only decides WHICH inputs produce a
/// payload: `narrowWide x = some _` iff `fitsIN (toIntW x)`, the exact
/// predicate the program's `fits_i64` computes (already two-sidedly cited).
///
/// SYNC DISCIPLINE: these two definitions join the checked model's
/// synchronized copies — the client kernel text, this seeder, the trust-certify
/// def-eq oracle fixture, and the probe islands. Change all of them together.
fn seed_narrow_model(
    env: &mut Environment,
    from: MachineSIntWidth,
    to: MachineSIntWidth,
) -> Result<(), String> {
    seed_checked_model(env, to)?;
    seed_checked_model(env, from)?;
    let (from_bits, to_bits) = (from.bits(), to.bits());
    let (wide, narrow) = (Domain::Signed(from), Domain::Signed(to));
    let (wide_ty, narrow_ty) = (wide.ty(), narrow.ty());
    let option_ty = Domain::OptionSigned(to).ty();
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
    let c = |s: &str| Expr::const_(Name::from_string(s), vec![]);

    // trunc: fun (v : BitVec FROM) => BitVec.ofNat TO (BitVec.toNat FROM v)
    let trunc_name = trunc_model_name(from_bits, to_bits);
    let trunc_body = narrow.bitvec_of_nat(wide.bitvec_to_nat(Expr::bvar(0))?)?;
    seed_decl(
        env,
        &trunc_name,
        Expr::arrow(wide_ty.clone(), narrow_ty.clone()),
        Expr::lam(BinderInfo::Default, wide_ty.clone(), trunc_body),
    )?;

    // narrow: the two-arm Bool `match` on the guard, spelled EXACTLY as the
    // island elaborator produces it — `Bool.casesOn.{1}` with an anonymous
    // motive, the scrutinee, then the minors in CONSTRUCTOR order (`false`
    // first, so `none` is the third argument and `some` the fourth).
    let guard = Expr::app(
        c(&checked_model_name("fitsI", to_bits)),
        Expr::app(c(&checked_model_name("toInt", from_bits)), Expr::bvar(0)),
    );
    let body = Expr::apps(
        Expr::const_(Name::from_string("Bool.casesOn"), vec![Level::succ(Level::zero())]),
        [
            Expr::lam(BinderInfo::Default, bool_ty, option_ty.clone()),
            guard,
            Expr::app(
                Expr::const_(Name::from_string("Option.none"), vec![Level::zero()]),
                narrow_ty.clone(),
            ),
            Expr::apps(
                Expr::const_(Name::from_string("Option.some"), vec![Level::zero()]),
                [narrow_ty, Expr::app(c(&trunc_name), Expr::bvar(0))],
            ),
        ],
    );
    seed_decl(
        env,
        &narrow_model_name(from_bits, to_bits),
        Expr::arrow(wide_ty.clone(), option_ty),
        Expr::lam(BinderInfo::Default, wide_ty, body),
    )
}

/// Mint an E6 [`Admission`] for a WIDTH-GUARDED NARROWING function — the body
/// of `veripb_core_proved::guard::narrow`, recognized as
/// `trust_types::admissible_body::AdmissibleBody::GuardedNarrow`. The model of
/// [`seed_narrow_model`] is seeded ONCE and the minted defining equation is
/// just the applied seeded constant:
/// `fun p0 … p_{n-1} => trust_checked_narrowI128toI64 p_param`, at type
/// `T0 → … → Option (BitVec 64)`, FULL-KERNEL-CHECKED by `add_decl`.
///
/// MONOMORPHIC this increment: only `(i128 → Option<i64>)` is admitted. Other
/// source/target widths PARK — their MIR bound spellings are unmeasured, and
/// admitting an unmeasured guard is exactly the failure this lane exists to
/// prevent.
///
/// SOUNDNESS: `add_decl` guarantees well-typedness, not fidelity. Fidelity
/// rests on (a) the recognizer's exactness — the body IS the pinned
/// `i64::MIN`/`i64::MAX` conjunction guard over exactly this parameter, with
/// `Some` of exactly its truncation on the guard-true path and `None` on both
/// guard-false paths — and (b) the seeded model being the faithful TOTAL model
/// of that body, truncation included (see [`seed_narrow_model`]). The §5.7 NEG
/// fixtures pin that an arms-swapped, a wrong-truncation-width, or a
/// wrong-guard-width island model is CAUGHT by definitional comparison, not
/// silently green.
pub fn admit_guarded_narrow_function(
    env: &mut Environment,
    kernel_const: &str,
    param_domains: &[Domain],
    from: MachineSIntWidth,
    to: MachineSIntWidth,
    param: usize,
) -> Result<Admission, String> {
    let n = param_domains.len();
    if param >= n {
        return Err(format!(
            "guarded-narrow parameter index {param} is out of range for a \
             {n}-parameter function"
        ));
    }
    if from != MachineSIntWidth::I128 || to != MachineSIntWidth::I64 {
        return Err(format!(
            "the guarded-narrow lane is monomorphic this increment: only \
             `i128` -> `Option<i64>` is admitted, not `{}` -> `{}`",
            Domain::Signed(from).rust_name(),
            Domain::OptionSigned(to).rust_name()
        ));
    }
    let wide = Domain::Signed(from);
    if param_domains[param] != wide {
        return Err(format!(
            "the guarded-narrow parameter must live at the source carrier `{}`, not `{}`",
            wide.rust_name(),
            param_domains[param].rust_name()
        ));
    }
    seed_narrow_model(env, from, to)?;
    let body = Expr::app(
        Expr::const_(Name::from_string(&narrow_model_name(from.bits(), to.bits())), vec![]),
        Expr::bvar((n - 1 - param) as u32),
    );
    // Fold in REVERSE parameter order so the OUTERMOST binder is `p0` and the
    // de Bruijn index above (`n - 1 - param`) names the intended parameter
    // even when the parameters do not share one carrier.
    let lam = param_domains
        .iter()
        .rev()
        .fold(body, |acc, d| Expr::lam(BinderInfo::Default, d.ty(), acc));
    let arrow_ty = param_domains
        .iter()
        .rev()
        .fold(Domain::OptionSigned(to).ty(), |acc, d| Expr::arrow(d.ty(), acc));
    env.add_decl(Declaration::Definition {
        name: Name::from_string(kernel_const),
        level_params: vec![],
        type_: arrow_ty,
        value: lam,
        is_reducible: true,
    })
    .map_err(|e| format!("kernel rejected the guarded-narrow defining equation: {e:?}"))?;
    Ok(Admission::reflected(kernel_const, n)
        .with_declared_signature(Some(Domain::OptionSigned(to)), Some(DeclaredCarriers::of_domains(param_domains, &Domain::OptionSigned(to)))))
}

/// Structurally replace every bare `result` identifier in a clause AST with
/// `replacement` (the `self_fn(params…)` call). Only the clause-expression node
/// shapes the elaborator supports are traversed; anything else is returned
/// unchanged (it will fail closed in the elaborator, not here). NOTE: a `result`
/// appearing as a call's CALLEE is not a clause variable and is left alone —
/// consistent with `collect_vars`, which never treats a callee path as a variable.
/// Rewrite every `result.<field>` to the per-field E6 import minted for it.
///
/// An aggregate return has no single kernel term, so `result` alone is not
/// denotable -- but each FIELD is, and `admit_function_fields_into` mints one
/// constant per field under the spellable key `<def_path>__field_<name>`. This
/// substitutes that call, which is why projecting an aggregate return no longer
/// needs a struct carrier in the fragment.
///
/// ORDER AGREEMENT is enforced exactly as the whole-function path enforces it:
/// the minted parameter list must equal the compiler's, because a disagreement
/// is the one failure the kernel cannot catch -- the goal still types while a
/// theorem about one binder discharges a clause about another. The synthesized
/// call is also round-tripped through `callee_path`, so a key that re-resolves
/// to a different item fails closed.
fn mentions_result_field(e: &SynExpr) -> bool {
    match e {
        SynExpr::Field(f) => {
            matches!(&*f.base, SynExpr::Path(p) if p.path.is_ident("result"))
                || mentions_result_field(&f.base)
        }
        SynExpr::Paren(p) => mentions_result_field(&p.expr),
        SynExpr::Unary(u) => mentions_result_field(&u.expr),
        SynExpr::Binary(b) => mentions_result_field(&b.left) || mentions_result_field(&b.right),
        SynExpr::Call(c) => c.args.iter().any(mentions_result_field),
        _ => false,
    }
}

fn rewrite_result_fields(
    e: &SynExpr,
    self_fn_name: &str,
    param_names: &[String],
    facets: &FacetTable,
) -> Result<SynExpr, String> {
    Ok(match e {
        // `result.<field>` — the base must be `result` ITSELF; a projection of
        // anything else names a parameter and is left alone.
        SynExpr::Field(f)
            if matches!(&*f.base, SynExpr::Path(p) if p.path.is_ident("result")) =>
        {
            let syn::Member::Named(ident) = &f.member else {
                return Err(
                    "a positional projection of `result` (`result.0`) is outside the clause \
                     fragment; name the field".to_string(),
                );
            };
            let key = format!("{self_fn_name}__field_{ident}");
            let Some(admission) = facets.admitted(&key) else {
                // Say WHICH of the two conditions failed. `admitted` requires an
                // admissible facet record AND a minted admission, and one
                // message for both is unreadable: a mint that never ran and a
                // mint whose record did not follow it look identical.
                let minted = facets.has_admission(&key);
                let record = facets.get(&key).map(FnFacets::admissible);
                return Err(format!(
                    "`result.{ident}` has no kernel denotation under `{key}`: \
                     admission_minted={minted}, facet_record={record:?}. Both are required -- a \
                     field is minted only when its shape and operands are scalars the mint can \
                     state, and the key then needs the parent's facet record installed beside it."
                ));
            };
            if let Some(minted) = admission.param_names.as_ref().filter(|minted| *minted != param_names) {
                return Err(format!(
                    "the clause's parameter list {param_names:?} disagrees with the list the \
                     per-field import of `{key}` was minted over ({minted:?}); the two \
                     flattenings of one signature must agree exactly, so the discharge fails \
                     closed"
                ));
            }
            let call_src = format!("{key}({})", param_names.join(", "));
            let call: SynExpr = syn::parse_str(&call_src)
                .map_err(|e| format!("internal: could not build field call `{call_src}`: {e}"))?;
            let SynExpr::Call(call_expr) = &call else {
                return Err(format!("internal: `{call_src}` did not parse as a call"));
            };
            if callee_path(call_expr) != key {
                return Err(format!(
                    "the per-field import `{key}` is not spellable as a spec call; binding \
                     `result.{ident}` to it fails closed"
                ));
            }
            call
        }
        SynExpr::Paren(p) => {
            let mut p = p.clone();
            p.expr = Box::new(rewrite_result_fields(&p.expr, self_fn_name, param_names, facets)?);
            SynExpr::Paren(p)
        }
        SynExpr::Unary(u) => {
            let mut u = u.clone();
            u.expr = Box::new(rewrite_result_fields(&u.expr, self_fn_name, param_names, facets)?);
            SynExpr::Unary(u)
        }
        SynExpr::Binary(b) => {
            let mut b = b.clone();
            b.left = Box::new(rewrite_result_fields(&b.left, self_fn_name, param_names, facets)?);
            b.right = Box::new(rewrite_result_fields(&b.right, self_fn_name, param_names, facets)?);
            SynExpr::Binary(b)
        }
        SynExpr::Call(c) => {
            let mut c = c.clone();
            c.args = c
                .args
                .iter()
                .map(|a| rewrite_result_fields(a, self_fn_name, param_names, facets))
                .collect::<Result<_, _>>()?;
            SynExpr::Call(c)
        }
        other => other.clone(),
    })
}

/// The DECLARED carriers of a call's callee, when the ambient admission table
/// records them (see [`Admission::carriers`]). `None` for an unadmitted callee,
/// for an admission that recorded no declaration, and for a record whose length
/// contradicts the recorded arity — the last so that two disagreeing reads of
/// one declaration can never be indexed against each other.
fn typed_callee_carriers(c: &syn::ExprCall) -> Option<DeclaredCarriers> {
    // I0: STEERING ONLY (see [`ambient_admission`]) — a declared carrier is a
    // CHECK on an argument, never a binding.
    let callee = callee_path(c);
    ADMISSION_FACETS.with(|slot| {
        let borrow = slot.borrow();
        let admission = borrow.as_ref()?.admitted(&callee)?;
        admission
            .carriers
            .as_ref()
            .filter(|carriers| carriers.params.len() == admission.arity)
            .cloned()
    })
}

fn has_typed_callee_carriers(c: &syn::ExprCall) -> bool {
    let callee = callee_path(c);
    ADMISSION_FACETS.with(|slot| {
        slot.borrow().as_ref().and_then(|table| table.admitted(&callee)).is_some_and(|admission| {
            admission
                .carriers
                .as_ref()
                .is_some_and(|carriers| carriers.params.len() == admission.arity)
        })
    })
}

/// Collect the AMBIENT free variables of an atom — those that are operands of
/// the atom itself, skipping the ARGUMENTS of a call whose callee declares its
/// own parameter carriers.
///
/// Why the skip (E6/E9 widening increment 8). An argument of a typed call is
/// not an operand of the enclosing comparison: it is typed by the CALLEE, whose
/// declaration is the authority on its width. Counting it as an operand is what
/// made `result == eq_ok_isl(machine, truth)` — an island declared
/// `(m : BitVec 64) (t : BitVec 128)`, applied to an `i64` and an `i128`
/// parameter — report "mixed domains in one comparison" for two widths that
/// were never in one comparison to begin with.
///
/// This is deliberately NOT [`collect_vars`], which must keep visiting call
/// arguments: a variable occurring only there is still FREE in the clause, and
/// the exact-binding gate has to see it. The two walks answer different
/// questions and the split is the point.
fn collect_ambient_vars(e: &SynExpr, out: &mut Vec<String>) {
    match e {
        SynExpr::Paren(p) => collect_ambient_vars(&p.expr, out),
        SynExpr::Cast(cast) => collect_ambient_vars(&cast.expr, out),
        SynExpr::Binary(b) => {
            collect_ambient_vars(&b.left, out);
            collect_ambient_vars(&b.right, out);
        }
        SynExpr::Unary(u) => collect_ambient_vars(&u.expr, out),
        // THE ONE DIFFERENCE from `collect_vars`: a call whose callee declares
        // its own parameter carriers contributes NO ambient operands.
        SynExpr::Call(c) => {
            if !has_typed_callee_carriers(c) {
                for arg in &c.args {
                    collect_ambient_vars(arg, out);
                }
            }
        }
        SynExpr::MethodCall(m) => {
            collect_ambient_vars(&m.receiver, out);
            for arg in &m.args {
                collect_ambient_vars(arg, out);
            }
        }
        // Leaves (bare paths, depth-1 field projections, literals) have no call
        // structure to skip, so they reuse [`collect_vars`] verbatim — there is
        // exactly one implementation of "what names a variable", including its
        // `None`-constructor exclusion.
        leaf => collect_vars(leaf, out),
    }
}

/// The single domain the atom's AMBIENT operands determine, or `None` when
/// nothing in it does (a variable-free atom, or one whose only variables sit
/// inside a typed call's argument list).
///
/// Mixed ambient operands are the genuine error this has always reported: two
/// values of different widths compared with no cast and no typed callee to
/// justify it. That refusal is unchanged.
fn resolved_atom_domain(
    atom: &SynExpr,
    var_domains: &BTreeMap<String, Domain>,
) -> Result<Option<Domain>, String> {
    let mut vs = Vec::new();
    collect_ambient_vars(atom, &mut vs);
    common_var_domain(&vs, var_domains)
}

/// [`resolved_atom_domain`] over EVERY free variable of the atom, call
/// arguments included — the pre-increment computation, verbatim. It stays the
/// FIRST thing [`atom_domain`] tries, so every clause that resolved before this
/// increment resolves to the same domain now.
fn resolved_atom_domain_all_vars(
    atom: &SynExpr,
    var_domains: &BTreeMap<String, Domain>,
) -> Result<Option<Domain>, String> {
    let mut vs = Vec::new();
    collect_vars(atom, &mut vs);
    common_var_domain(&vs, var_domains)
}

/// The one domain a list of clause variables shares, `None` for an empty list,
/// and the long-standing "mixed domains in one comparison" refusal when they
/// disagree.
fn common_var_domain(
    vs: &[String],
    var_domains: &BTreeMap<String, Domain>,
) -> Result<Option<Domain>, String> {
    let mut dom: Option<Domain> = None;
    for v in vs {
        let Some(d) = var_domains.get(v) else {
            // Not a bound clause variable (main's C6 lane, woven into wip's
            // resolver): a bare identifier naming an ambient-admitted
            // ZERO-ARITY constant is a citation, and its recorded return
            // domain is term evidence exactly like an admitted CALLEE's --
            // steering only, merged fail-closed, and an admission without a
            // recorded domain contributes nothing. A PARAMETERED admission
            // cited bare is refused with the fix named. Bindings win over
            // admissions, the same precedence as everywhere on this path —
            // including I0's: a name the compiler records as a Rust binding of
            // the specified function refuses here rather than being typed as a
            // citation.
            if let Some(admission) = ambient_bare_admission(v)? {
                if admission.arity != 0 {
                    return Err(format!(
                        "admitted `{v}` has arity {} and must be applied (`{v}(…)`); a \
                         bare reference to a parametered definition is outside the term \
                         fragment",
                        admission.arity
                    ));
                }
                if let Some(found) = admission.return_domain() {
                    merge_term_domain_evidence(
                        &mut dom,
                        found.clone(),
                        &format!("admitted constant `{v}`"),
                    )?;
                }
                continue;
            }
            return Err(format!("unbound variable `{v}`"));
        };
        match &dom {
            None => dom = Some(d.clone()),
            Some(existing) if existing == d => {}
            Some(existing) => {
                return Err(format!(
                    "mixed domains in one comparison ({existing:?} and {d:?}) — the operands of a \
                     single comparison must share a type"
                ));
            }
        }
    }
    Ok(dom)
}

/// The domain the RESULTS of the admitted calls in an atom's ambient positions
/// agree on, or `None` when nothing determines one.
///
/// SOUNDNESS — every answer comes from a DECLARATION, and the two sources are
/// ranked by how much they know:
///
///  1. an [`Admission::ret_domain`] a compiler MINT recorded. That is the exact
///     `Domain` the mint built its declaration at, so it is not merely
///     authoritative, it is the original.
///  2. failing that, the declared result CARRIER, but only through
///     [`Carrier::unique_domain`] — the PARTIAL inverse of `Domain -> Carrier`,
///     defined exactly where the carrier has ONE preimage and UNDEFINED on
///     `BitVec N`, whose three preimages disagree about literal range. This is
///     the same discipline (and the same caveat) as
///     `trust_certify::clean_island::island_definition_signature`: a numeric
///     BitVec codomain answers `None` and the caller keeps its old default,
///     rather than being guessed at.
///
/// Two declarations disagreeing is an error, not a preference. Once a domain is
/// fixed, EVERY ambient call's declared result carrier is checked against it
/// ([`check_ambient_call_result_carriers`]) — including the islands that could
/// not contribute one under rule 2 — so the relation carrier a clause is built
/// at can never contradict a callee's declared type.
fn atom_call_result_domain(atom: &SynExpr) -> Result<Option<Domain>, String> {
    let mut calls = Vec::new();
    collect_ambient_calls(atom, &mut calls);
    let mut dom: Option<Domain> = None;
    for c in &calls {
        // I0: STEERING ONLY (see [`ambient_admission`]) — this fixes the
        // comparison's domain, and `elab_term` refuses a shadowed callee.
        let Some(admission) = ambient_admission(&callee_path(c)) else { continue };
        let declared = admission
            .return_domain().cloned()
            .or_else(|| typed_callee_carriers(c).and_then(|cs| cs.ret.unique_domain()));
        let Some(d) = declared else { continue };
        match &dom {
            None => dom = Some(d),
            Some(existing) if *existing == d => {}
            Some(existing) => {
                return Err(format!(
                    "mixed domains in one comparison ({existing:?} and {d:?}) — the operands of a \
                     single comparison must share a type"
                ));
            }
        }
    }
    let Some(dom) = dom else { return Ok(None) };
    check_ambient_call_result_carriers(atom, &dom)?;
    Ok(Some(dom))
}

/// Every admitted call in the atom's ambient positions must declare its RESULT
/// at the carrier the atom is being built at. A disagreement is an error — the
/// same "check, never coerce" rule the argument positions get in [`elab_term`],
/// applied to the relation carrier.
///
/// The carrier half refuses only on paths that did not exist before increment 8 (a
/// variable-free atom and a recovered mixed-domain atom, including the step-1
/// domain [`step_one_result_carrier_conflict`] sends there), so it can refuse
/// nothing that used to be accepted; on those paths it turns what would have
/// been a downstream ill-typed goal into a named refusal at the clause.
///
/// EQUAL CARRIERS ARE NOT EQUAL DOMAINS (I0, TG15 open item 3). `BitVec 128`
/// is the carrier of `u128` and of `i128`, so a carrier check alone passed
/// `result >= 0` on a `u128 -> i128` kernel at step 1's `u128`, the parameter's
/// UNSIGNED order over a signed result: a goal true of every input. A result
/// domain the callee's mint recorded is the authority on how its value is read,
/// so it is compared too, by reading ([`Domain::reads_like`]) rather than by
/// name. Where the relation took its domain from the recorded results
/// themselves ([`atom_call_result_domain`]) the two always agree.
///
/// A BARE call atom's own result is not compared by reading. Such an atom is
/// no relation: [`atom_domain`] hands its domain to [`elab_term`] as the domain
/// of the call's ARGUMENTS (`p(widen(flag), x)` read as `p(..) = true`), so a
/// `bool` or `Option<iN>` result is not read at it. Comparing it refused a
/// well-typed clause the carrier check had always accepted.
fn check_ambient_call_result_carriers(atom: &SynExpr, dom: &Domain) -> Result<(), String> {
    let mut bare = atom;
    while let SynExpr::Paren(p) = bare {
        bare = &p.expr;
    }
    let root = match bare {
        SynExpr::Call(c) => Some(c),
        _ => None,
    };
    let mut calls = Vec::new();
    collect_ambient_calls(atom, &mut calls);
    for c in &calls {
        if let Some(carriers) = typed_callee_carriers(c).filter(|cs| cs.ret != dom.carrier()) {
            return Err(format!(
                "admitted `{}` declares its result at carrier `{}`, but the comparison is at \
                 carrier `{}` (`{}`); a clause is checked against the callee's declared type \
                 and is never coerced to it",
                callee_path(c),
                carriers.ret.clean_name(),
                dom.carrier().clean_name(),
                dom.rust_name()
            ));
        }
        if root.is_some_and(|r| std::ptr::eq(r, *c)) {
            continue;
        }
        if let Some(declared) = call_ret_domain(c).filter(|d| !d.reads_like(dom)) {
            return Err(format!(
                "admitted `{}` returns a `{}` (carrier `{}`), but the comparison is at `{}` \
                 (carrier `{}`); a clause is checked against the callee's declared result \
                 domain, not only its carrier, and is never coerced to it",
                callee_path(c),
                declared.rust_name(),
                declared.carrier().clean_name(),
                dom.rust_name(),
                dom.carrier().clean_name()
            ));
        }
    }
    Ok(())
}

/// Whether [`atom_domain`]'s step-1 domain `dom` is contradicted by a typed
/// OPERAND of `atom`: `Some(refusal)` when an admitted call in an ambient
/// position declares its result at a carrier other than `dom`'s, `None` when
/// step 1 stands.
///
/// Step 1 types an atom by every variable in it, a typed call's arguments
/// included. When such a call is an operand of the atom (a side of a
/// comparison, or of arithmetic), what the relation compares is the call's
/// RESULT, so a result carrier other than `dom`'s means the goal step 1 would
/// build cannot typecheck (`Eq Bool` over two `UInt8` calls for
/// `result == spec(a, b)` in a `bool, bool -> u8` function).
///
/// A BARE call atom is not tested: it is a proposition or a term in its own
/// right (`f(x, 3)` read as `f(x, 3) = true`), not a relation over its result,
/// and its callers hand step 1's domain to `elab_term` as the ARGUMENT domain,
/// the fallback [`argument_domain`] gives a literal argument its siblings do
/// not type.
///
/// An atom with a CAST anywhere in it ([`contains_cast`]) is not tested either.
/// A cast gives the operand it wraps its target's carrier, so a call under one
/// is not compared at its result carrier, and every such atom already has its
/// own path: under [`ClauseMode::ProofLift`] the relation is built by
/// [`elab_math_relation`], and in every other mode the cast is refused as
/// `unsupported term shape`, a message kept to the byte. Testing it here would
/// replace that refusal with a carrier refusal that names the wrong cause
/// (`result as nat == nat_id(x as nat)` is not a comparison at `UInt64`).
///
/// Under [`ClauseMode::ProofLift`] (the E9 citation lane) the exemption is only
/// for a cast in an AMBIENT position ([`contains_ambient_cast`]). A cast inside
/// a typed call's ARGUMENT list is typed by that callee's declared parameter
/// (the lift row of [`elab_term`]'s call arm), not by the relation, so it says
/// nothing about the relation's carrier: `result == bucket_spec(x as nat)` on
/// `fn bucket(x: u32) -> u8` relates two `UInt8` results, and keeping step 1's
/// `UInt32` there built `@Eq UInt32` over them, the ill-typed goal TG15 is
/// about. In every other mode a cast anywhere is refused, so the broad
/// exemption stays and so does that refusal's text.
fn step_one_result_carrier_conflict(atom: &SynExpr, dom: &Domain) -> Option<String> {
    let mut bare = atom;
    while let SynExpr::Paren(p) = bare {
        bare = &p.expr;
    }
    let cast_exempt = if has_ambient_proof_lift() {
        contains_ambient_cast(atom)
    } else {
        contains_cast(atom)
    };
    if matches!(bare, SynExpr::Call(_) | SynExpr::MethodCall(_)) || cast_exempt {
        return None;
    }
    check_ambient_call_result_carriers(atom, dom).err()
}

/// Whether `e` carries a cast in an AMBIENT position: [`contains_cast`] with the
/// walk of [`collect_ambient_calls`], so a cast inside the argument list of a
/// call whose callee declares its own parameter carriers does not count (that
/// callee's declaration types it).
fn contains_ambient_cast(e: &SynExpr) -> bool {
    match e {
        SynExpr::Cast(_) => true,
        SynExpr::Paren(p) => contains_ambient_cast(&p.expr),
        SynExpr::Unary(u) => contains_ambient_cast(&u.expr),
        SynExpr::Binary(b) => contains_ambient_cast(&b.left) || contains_ambient_cast(&b.right),
        SynExpr::Call(c) => {
            !has_typed_callee_carriers(c) && c.args.iter().any(contains_ambient_cast)
        }
        SynExpr::MethodCall(m) => {
            contains_ambient_cast(&m.receiver) || m.args.iter().any(contains_ambient_cast)
        }
        SynExpr::Field(f) => contains_ambient_cast(&f.base),
        _ => false,
    }
}

/// The CALL expressions in an atom's ambient positions — the same walk as
/// [`collect_ambient_vars`], so a call nested inside a typed call's argument
/// list is skipped for the same reason its variables are: it is typed by that
/// callee's declaration, not by the enclosing comparison.
fn collect_ambient_calls<'a>(e: &'a SynExpr, out: &mut Vec<&'a syn::ExprCall>) {
    match e {
        SynExpr::Paren(p) => collect_ambient_calls(&p.expr, out),
        SynExpr::Cast(cast) => collect_ambient_calls(&cast.expr, out),
        SynExpr::Binary(b) => {
            collect_ambient_calls(&b.left, out);
            collect_ambient_calls(&b.right, out);
        }
        SynExpr::Unary(u) => collect_ambient_calls(&u.expr, out),
        SynExpr::Call(c) => {
            out.push(c);
            if !has_typed_callee_carriers(c) {
                for arg in &c.args {
                    collect_ambient_calls(arg, out);
                }
            }
        }
        _ => {}
    }
}

/// The domain ONE argument of a typed call is elaborated at.
///
/// The order below is an authority ranking, not a search for something that
/// works:
///   1. the argument's OWN ambient variables — their domains come from the
///      clause bindings, i.e. from the contracted function's Rust signature;
///   2. failing that, the domain the call's OTHER arguments jointly determine,
///      which is exactly what the single-ambient-domain elaborator used before
///      this increment and keeps a literal beside a typed sibling unchanged;
///   3. failing that, the enclosing atom's domain — again the pre-increment
///      source for a variable-free argument.
///
/// Nothing here reads the callee's declared carrier: that carrier is the CHECK
/// applied to the answer (in [`elab_term`]'s call arm), and letting it also be
/// the source would invert the non-injective `Domain -> Carrier` map (see
/// [`Carrier`]). A mixed-domain ARGUMENT — `f(x + y)` with `x : i64` and
/// `y : i128` — is still the genuine error it always was.
fn argument_domain(
    arg: &SynExpr,
    siblings: &syn::ExprCall,
    var_domains: &BTreeMap<String, Domain>,
    ambient: &Domain,
) -> Result<Domain, String> {
    if let Some(dom) = resolved_atom_domain(arg, var_domains)? {
        return Ok(dom);
    }
    // A NESTED typed call as an argument answers for itself: its own callee
    // declared what it returns.
    if let Some(dom) = atom_call_result_domain(arg)? {
        return Ok(dom);
    }
    let mut vs = Vec::new();
    for other in &siblings.args {
        collect_ambient_vars(other, &mut vs);
    }
    let mut sibling_dom: Option<Domain> = None;
    for v in &vs {
        let Some(d) = var_domains.get(v) else { continue };
        match &sibling_dom {
            None => sibling_dom = Some(d.clone()),
            // Siblings at DIFFERENT widths say nothing about this argument;
            // fall through to the ambient rather than pick one of them.
            Some(existing) if existing == d => {}
            Some(_) => return Ok(ambient.clone()),
        }
    }
    Ok(sibling_dom.unwrap_or_else(|| ambient.clone()))
}

/// The declared RESULT carrier of `arg` when it is (up to parentheses) a call
/// whose callee records its carriers but whose result no declaration names a
/// domain for: no recorded return domain, and a result carrier with more than
/// one Rust preimage (`BitVec n`). `None` for every other term, including a
/// typed call whose result domain IS determined, which keeps answering for
/// itself through [`argument_domain`].
///
/// A CHECK value only (I0): [`elab_term`] compares it with the enclosing
/// callee's declared parameter carrier, and it never becomes a [`Domain`].
fn undetermined_call_result_carrier(arg: &SynExpr) -> Result<Option<Carrier>, String> {
    let mut bare = arg;
    while let SynExpr::Paren(p) = bare {
        bare = &p.expr;
    }
    let SynExpr::Call(c) = bare else {
        return Ok(None);
    };
    let Some(carriers) = typed_callee_carriers(c) else {
        return Ok(None);
    };
    if atom_call_result_domain(bare)?.is_some() {
        return Ok(None);
    }
    Ok(Some(carriers.ret))
}

/// Format a `syn::Path` as `seg0::seg1::…` without allocating an intermediate
/// `Vec<String>` of individual segments.
fn path_spelling(path: &syn::Path) -> String {
    if let Some(ident) = path.get_ident() {
        return ident.to_string();
    }
    let mut out = String::new();
    for (idx, seg) in path.segments.iter().enumerate() {
        if idx > 0 {
            out.push_str("::");
        }
        use std::fmt::Write;
        let _ = write!(&mut out, "{}", seg.ident);
    }
    out
}

/// The callee path of a call expression, exactly as the facet/admission table
/// keys it (`min` or `cmp::min`). A non-path callee has no item identity and is
/// reported as `<expression>`, which never matches an admission key — so it
/// stays fail-closed.
fn callee_path(c: &syn::ExprCall) -> String {
    match &*c.func {
        SynExpr::Path(p) => path_spelling(&p.path),
        _ => "<expression>".to_string(),
    }
}

/// The E6 return domain of a CALL whose callee is in the ambient admission
/// table, or `None` for an unadmitted callee / an admission that does not
/// record one (see [`Admission::ret_domain`]).
fn call_ret_domain(c: &syn::ExprCall) -> Option<Domain> {
    // I0: STEERING ONLY (see [`ambient_admission`]).
    let callee = callee_path(c);
    ADMISSION_FACETS.with(|slot| {
        slot.borrow().as_ref()?.admitted(&callee)?.return_domain().cloned()
    })
}

/// The `Option<iN>` payload width of a CALL whose callee is admitted with an
/// [`Domain::OptionSigned`] return domain, else `None`.
///
/// Parentheses are looked through, as [`elab_option_term`] and
/// [`option_constructor_form`] do: `(result) == Some(a)` is the same Option
/// equality as `result == Some(a)`, and missing it typed the relation from the
/// constructor's argument instead (TG15).
fn call_option_ret_width(e: &SynExpr) -> Option<MachineSIntWidth> {
    match e {
        SynExpr::Paren(p) => call_option_ret_width(&p.expr),
        SynExpr::Call(c) => match call_ret_domain(c) {
            Some(Domain::OptionSigned(width)) => Some(width),
            _ => None,
        },
        _ => None,
    }
}

/// Whether `e` is an Option CONSTRUCTOR literal — `Some(..)` or `None` — whose
/// carrier must come from the OTHER side of the equality (a constructor alone
/// names no width).
fn option_constructor_form(e: &SynExpr) -> bool {
    match e {
        SynExpr::Paren(p) => option_constructor_form(&p.expr),
        SynExpr::Path(p) => p.path.is_ident("None"),
        SynExpr::Call(c) => matches!(&*c.func, SynExpr::Path(p) if p.path.is_ident("Some")),
        _ => false,
    }
}

/// Elaborate one side of an Option-carrier equality (checked-arith spec §3.3):
/// a `Some(..)`/`None` CONSTRUCTOR (typed at [`Domain::OptionSigned`] by
/// [`elab_term`]'s formers) or a call to an admitted function whose recorded
/// return domain is the SAME Option carrier (its ARGUMENTS keep their own
/// domain, recovered from the argument variables — exactly the Bool-lane
/// discipline in [`elab_bool_term`]). Everything else — a destructor, a bare
/// variable, an arithmetic term — fails closed with a named reason: this
/// increment has Option CONSTRUCTORS only.
fn elab_option_term(
    e: &SynExpr,
    vars: &[String],
    offset: u32,
    width: MachineSIntWidth,
    var_domains: &BTreeMap<String, Domain>,
) -> Result<Expr, String> {
    match e {
        SynExpr::Paren(p) => elab_option_term(&p.expr, vars, offset, width, var_domains),
        _ if option_constructor_form(e) => {
            elab_term(e, vars, offset, var_domains, &Domain::OptionSigned(width))
        }
        SynExpr::Call(c) => match call_option_ret_width(e) {
            Some(w) if w == width => {
                // The arguments keep their own (signed) carrier; only the
                // relation carrier is the Option. `elab_term`'s call arm
                // applies the admitted kernel constant.
                let arg_dom = atom_domain(e, var_domains)?;
                elab_term(e, vars, offset, var_domains, &arg_dom)
            }
            Some(w) => Err(format!(
                "admitted `{}` returns `{}`, but the other operand fixes the carrier \
                 `Option<i{}>` — the two sides of one equality must share a carrier",
                callee_path(c),
                Domain::OptionSigned(w).rust_name(),
                width.bits(),
            )),
            None => {
                // Reuse the canonical fail-closed call diagnostics from
                // `elab_term` (unadmitted callee / non-Option admission).
                match elab_term(e, vars, offset, var_domains, &Domain::OptionSigned(width)) {
                    Err(err) => Err(err),
                    Ok(_) => Err(format!(
                        "admitted `{}` does not record an `Option` return domain, so it \
                         cannot stand against an Option operand",
                        callee_path(c)
                    )),
                }
            }
        },
        _ => Err(
            "an Option-carrier operand must be `Some(<term>)`, `None`, or a call to an \
             admitted checked-arithmetic function; Option destructors (`unwrap`, `match`, \
             `?`) are outside this increment and fail closed"
                .into(),
        ),
    }
}

/// Whether `e` denotes a **`bool`-valued term** — something that can stand on
/// either side of a `Bool` equality and be elaborated by [`elab_bool_term`].
///
/// This is a syntactic classification of the CLAUSE, not a typing judgment: a
/// comparison is `bool`-valued in Rust whatever its operands are, and its
/// operands' own domain is decided separately by [`atom_domain`]. That split is
/// the whole point — `result == (a <= b)` has a `Bool` relation carrier and
/// `BitVec 64` operands, and conflating the two is what used to report the
/// nested comparison as a "mixed domains in one comparison" clause error.
fn bool_valued_term(e: &SynExpr, var_domains: &BTreeMap<String, Domain>) -> bool {
    match e {
        SynExpr::Paren(p) => bool_valued_term(&p.expr, var_domains),
        SynExpr::Lit(l) => matches!(&l.lit, Lit::Bool(_)),
        // A bare identifier or a dotted path (`c.flag`) is bool-valued exactly
        // when its DECLARED binding is `bool`; an unrecognized shape has no
        // binding and is not bool-valued.
        SynExpr::Path(_) | SynExpr::Field(_) => atom_var_name(e)
            .and_then(|name| var_domains.get(&name))
            .is_some_and(Domain::is_bool),
        SynExpr::Unary(u) if matches!(u.op, syn::UnOp::Not(_)) => {
            bool_valued_term(&u.expr, var_domains)
        }
        SynExpr::Binary(b) => match b.op {
            BinOp::Eq(_)
            | BinOp::Ne(_)
            | BinOp::Le(_)
            | BinOp::Lt(_)
            | BinOp::Ge(_)
            | BinOp::Gt(_) => true,
            BinOp::And(_) | BinOp::Or(_) => {
                bool_valued_term(&b.left, var_domains) && bool_valued_term(&b.right, var_domains)
            }
            _ => false,
        },
        SynExpr::Call(c) => call_ret_domain(c).is_some_and(|d| d.is_bool()),
        _ => false,
    }
}

/// Whether `e` is a `bool`-valued term that the PRE-EXISTING single-`Domain`
/// lane cannot elaborate: a nested comparison / `!` / `&&` / `||`, or a call to
/// an admitted `-> bool` function.
///
/// A bare `bool` binding and a `true`/`false` literal are deliberately NOT
/// "decided forms": `flag == true` already elaborates, byte-identically, on the
/// existing path, and routing it through the new lane would be a silent
/// re-encoding of a shape that discharges today. The new lane engages only when
/// at least one side genuinely needs it.
fn decided_bool_form(e: &SynExpr, var_domains: &BTreeMap<String, Domain>) -> bool {
    match e {
        SynExpr::Paren(p) => decided_bool_form(&p.expr, var_domains),
        SynExpr::Unary(u) if matches!(u.op, syn::UnOp::Not(_)) => {
            bool_valued_term(&u.expr, var_domains)
        }
        SynExpr::Binary(b) => match b.op {
            BinOp::Eq(_)
            | BinOp::Ne(_)
            | BinOp::Le(_)
            | BinOp::Lt(_)
            | BinOp::Ge(_)
            | BinOp::Gt(_) => true,
            BinOp::And(_) | BinOp::Or(_) => bool_valued_term(e, var_domains),
            _ => false,
        },
        SynExpr::Call(c) => call_ret_domain(c).is_some_and(|d| d.is_bool()),
        _ => false,
    }
}

/// Elaborate a `bool`-VALUED TERM (not a proposition) — the `Bool` inhabitant a
/// decidable check computes.
///
/// The encoding is not a free choice: a comparison elaborates to
/// `Decidable.decide <prop> <inst>` over the SAME `(prop, inst)` pair
/// [`decidable_comparison`] hands [`admit_comparison_function`], so a clause
/// `result == (a <= b)` on `fn le(a, b) -> bool { a <= b }` produces a goal
/// whose two sides are SYNTACTICALLY IDENTICAL after unfolding the import, and
/// `Eq.refl` closes it with nothing clever. Emitting `Iff` here instead — or any
/// other equivalent-but-differently-shaped proposition — would forfeit that and
/// force every author to hand-write a theorem for a fact the kernel closes by
/// reflexivity; the same iota-mismatch lesson as the select encoding
/// (docs/design/2026-07-25-select-encoding-ergonomics.md).
///
/// `>` / `>=` normalize by OPERAND SWAP (`a > b` ≡ `b < a`), matching what
/// [`elaborate_prop`] already does in proposition position, so the two lanes
/// cannot disagree about what `>` means.
///
/// Fail-closed: anything not in this grammar — an integer term, an unadmitted
/// call, a non-`bool` binding — is refused with a named reason rather than
/// guessed at.
fn elab_bool_term(
    e: &SynExpr,
    vars: &[String],
    offset: u32,
    var_domains: &BTreeMap<String, Domain>,
) -> Result<Expr, String> {
    let bool_dom = Domain::Bool;
    let bool_op = |name: &'static str, args: Vec<Expr>| {
        Expr::apps(Expr::const_(Name::interned(name), vec![]), args)
    };
    match e {
        SynExpr::Paren(p) => elab_bool_term(&p.expr, vars, offset, var_domains),
        SynExpr::Lit(l) => match &l.lit {
            Lit::Bool(b) => bool_dom.bool_lit(b.value),
            _ => Err("only a `true`/`false` literal is a boolean term".into()),
        },
        SynExpr::Path(_) | SynExpr::Field(_) => {
            let d = atom_domain(e, var_domains)?;
            if !d.is_bool() {
                return Err(format!(
                    "mixed domains in one comparison (Bool and {d:?}) — the operands of a \
                     single comparison must share a type"
                ));
            }
            elab_term(e, vars, offset, var_domains, &bool_dom)
        }
        SynExpr::Unary(u) if matches!(u.op, syn::UnOp::Not(_)) => {
            Ok(bool_op("Bool.not", vec![elab_bool_term(&u.expr, vars, offset, var_domains)?]))
        }
        SynExpr::Binary(b) if matches!(b.op, BinOp::And(_) | BinOp::Or(_)) => {
            let l = elab_bool_term(&b.left, vars, offset, var_domains)?;
            let r = elab_bool_term(&b.right, vars, offset, var_domains)?;
            Ok(bool_op(
                if matches!(b.op, BinOp::And(_)) { "Bool.and" } else { "Bool.or" },
                vec![l, r],
            ))
        }
        SynExpr::Binary(b) => {
            // The comparison's OPERAND domain, independent of the `Bool` this
            // whole term inhabits.
            let d = atom_domain(e, var_domains)?;
            let (cmp, negate, left, right) = match b.op {
                BinOp::Eq(_) => (SelectCmp::Eq, false, &*b.left, &*b.right),
                BinOp::Ne(_) => (SelectCmp::Eq, true, &*b.left, &*b.right),
                BinOp::Lt(_) => (SelectCmp::Lt, false, &*b.left, &*b.right),
                BinOp::Le(_) => (SelectCmp::Le, false, &*b.left, &*b.right),
                BinOp::Gt(_) => (SelectCmp::Lt, false, &*b.right, &*b.left),
                BinOp::Ge(_) => (SelectCmp::Le, false, &*b.right, &*b.left),
                _ => {
                    return Err(
                        "a boolean term must be a comparison, a connective (&& || !), a `bool` \
                         binding, or a call to an admitted `-> bool` function"
                            .into(),
                    );
                }
            };
            let l = elab_term(left, vars, offset, var_domains, &d)?;
            let r = elab_term(right, vars, offset, var_domains, &d)?;
            // `decidable_comparison` itself refuses `Bool`/`Nat` operands, so a
            // decided `flag1 == flag2` or a variable-free `1 <= 2` fails closed
            // here rather than minting an undecidable scrutinee.
            let (prop, inst) = decidable_comparison(&d, cmp, l, r)?;
            let decided = bool_op("Decidable.decide", vec![prop, inst]);
            Ok(if negate { bool_op("Bool.not", vec![decided]) } else { decided })
        }
        SynExpr::Call(c) => {
            let callee = callee_path(c);
            match call_ret_domain(c) {
                // The ARGUMENTS keep their own domain (recovered from the
                // argument variables, exactly as every other atom is typed);
                // only the relation carrier is `Bool`.
                Some(ret) if ret.is_bool() => {
                    let arg_dom = atom_domain(e, var_domains)?;
                    elab_term(e, vars, offset, var_domains, &arg_dom)
                }
                Some(ret) => Err(format!(
                    "admitted `{callee}` returns `{}`, not `bool`, so it is not a boolean term",
                    ret.rust_name()
                )),
                // An UNADMITTED callee gets the single canonical E6 fail-closed
                // diagnostic (produced by `elab_term`, so there is exactly one
                // copy of it); an ADMITTED one with no recorded return domain
                // is refused for precisely that reason rather than assumed to
                // be `bool`.
                None => match elab_term(e, vars, offset, var_domains, &Domain::Nat) {
                    Err(e6) => Err(e6),
                    Ok(_) => Err(format!(
                        "admitted `{callee}` records no return domain, so it cannot be read as a \
                         `bool` term; restate the island definition with a `Bool` codomain"
                    )),
                },
            }
        }
        _ => Err("a boolean term must be a comparison, a connective (&& || !), a `bool` binding, \
                  or a call to an admitted `-> bool` function"
            .into()),
    }
}

impl Admission {
    /// Attach the DECLARED island signature (E6 carrier record + result
    /// domain). Recording only; `None` stays fail-closed for every consumer.
    #[must_use]
    pub fn with_declared_signature(
        mut self,
        ret_domain: Option<Domain>,
        carriers: Option<DeclaredCarriers>,
    ) -> Self {
        self.return_domain = ret_domain;
        self.carriers = carriers;
        self
    }

    /// Record the mint's DERIVED clause-side parameter list (increment 7).
    #[must_use]
    pub fn with_param_names(mut self, names: Vec<String>) -> Self {
        self.param_names = Some(names);
        self
    }

    /// Trust (ref-self I1): mark this import as minted over a SEMANTIC VIEW of
    /// the extracted body rather than over the body, and restrict it to the
    /// self-call position. See the two fields' docs.
    ///
    /// The two go together deliberately and there is no way to set one without
    /// the other: a view import that could be CALLED from a clause would make
    /// "the goal rests on a view" a whole-clause question instead of a
    /// one-admission one, and the disclosure would have to be re-derived at
    /// every reporting site.
    #[must_use]
    pub fn with_view(mut self, view: impl Into<String>) -> Self {
        self.view = Some(view.into());
        self.self_result_only = true;
        self
    }

    /// The name of the semantic view this import was minted over, if any. The
    /// compiler reads it to DISCLOSE; nothing here grades.
    #[must_use]
    pub fn view(&self) -> Option<&str> {
        self.view.as_deref()
    }

    /// Whether this admission may be named only as the spliced self-call.
    #[must_use]
    pub fn is_self_result_only(&self) -> bool {
        self.self_result_only
    }
}

#[cfg(test)]
mod machine_domain_tests {
    use clean_kernel::Environment;

    use super::*;

    #[test]
    fn machine_goal_elaborates_and_kernel_checks() {
        // A machine-typed clause quantifies over UInt64 with wrapping ops.
        let goal =
            elaborate_goal_typed("x + 0 == x", &[("x", "u64")]).expect("u64 clause must elaborate");
        let env = Environment::with_prelude();
        // The goal is a well-typed Prop (Sort 0): the kernel infers its type
        // without error — proving it is the citation's job, not this test's.
        let tc = clean_kernel::TypeChecker::new(&env);
        let _ = tc.infer_type(&goal).expect("machine goal must be well-typed in the prelude");
    }

    #[test]
    fn nat_and_machine_differ() {
        let nat_goal = elaborate_goal_typed("x + 0 == x", &[("x", "nat")]).unwrap();
        let u64_goal = elaborate_goal_typed("x + 0 == x", &[("x", "u64")]).unwrap();
        assert_ne!(nat_goal, u64_goal, "Nat and UInt64 goals must be distinct terms");
    }

    #[test]
    fn certified_monitor_nat_le() {
        let env = clean_kernel::Environment::with_prelude();
        // A certified monitor for `x <= y` over Nat: soundness kernel-checks.
        let m = certify_comparison_monitor(&env, "x <= y", &Domain::Nat)
            .expect("nat le monitor must certify");
        // The soundness goal + proof are a well-typed, kernel-accepted pair.
        let tc = clean_kernel::TypeChecker::new(&env);
        let _ty = tc.infer_type(&m.equivalence_goal).expect("goal well-typed");
        tc.check_type(&m.equivalence_proof, &m.equivalence_goal)
            .expect("proof inhabits the soundness goal");
    }

    #[test]
    fn certified_monitor_machine_lt_and_ge() {
        let env = clean_kernel::Environment::with_prelude();
        // Machine-domain monitor (decides through UInt64.toNat).
        certify_comparison_monitor(&env, "x < y", &Domain::Machine(MachineUIntWidth::U64))
            .expect("u64 lt monitor must certify");
        // `>=` reduces to `<=` with swapped operands and still certifies.
        certify_comparison_monitor(&env, "x >= y", &Domain::Nat)
            .expect("nat ge monitor must certify");
    }

    #[test]
    fn monitor_fragment_fails_closed() {
        let env = clean_kernel::Environment::with_prelude();
        // Non-comparison shapes are outside this monitor increment.
        assert!(certify_comparison_monitor(&env, "x == y", &Domain::Nat).is_err());
        assert!(certify_comparison_monitor(&env, "x <= y && x <= z", &Domain::Nat).is_err());
    }

    #[test]
    fn certified_monitor_nat_eq() {
        let env = clean_kernel::Environment::with_prelude();
        // A certified monitor for `x == y` over Nat: soundness kernel-checks via
        // Nat.eq_of_beq_eq_true.
        let m = certify_equality_monitor(&env, "x == y", &Domain::Nat)
            .expect("nat eq monitor must certify");
        let tc = clean_kernel::TypeChecker::new(&env);
        let _ = tc.infer_type(&m.equivalence_goal).expect("goal well-typed");
        tc.check_type(&m.equivalence_proof, &m.equivalence_goal)
            .expect("proof inhabits the soundness goal");
    }

    #[test]
    fn machine_equality_monitor_certifies() {
        let env = clean_kernel::Environment::with_prelude();
        let tc = clean_kernel::TypeChecker::new(&env);
        // Machine equality decides via `decide (Eq UInt64 a b)` with UInt64.decEq
        // and certifies through of_decide_eq_true (no toNat-injectivity needed).
        let m = certify_equality_monitor(&env, "x == y", &Domain::Machine(MachineUIntWidth::U64))
            .expect("u64 eq monitor must certify");
        let _ = tc.infer_type(&m.equivalence_goal).expect("goal well-typed");
        tc.check_type(&m.equivalence_proof, &m.equivalence_goal)
            .expect("proof inhabits the soundness goal");
        // Negated machine equality also certifies (dual cert via of_decide_eq_false).
        certify_monitor(&env, "!(x == y)", &Domain::Machine(MachineUIntWidth::U64))
            .expect("negated u64 eq must certify");
        // And machine equality composes inside connectives.
        certify_monitor(&env, "x < y && x == y", &Domain::Machine(MachineUIntWidth::U64))
            .expect("machine eq inside && must certify");
        certify_monitor(&env, "!(x < y && x == y)", &Domain::Machine(MachineUIntWidth::U64))
            .expect("negated machine compound with eq must certify");
    }

    #[test]
    fn certify_monitor_dispatches() {
        let env = clean_kernel::Environment::with_prelude();
        // The unified dispatcher routes `==` to the equality lane and `<=` to the
        // comparison lane — both certify.
        certify_monitor(&env, "x == y", &Domain::Nat).expect("eq dispatch certifies");
        certify_monitor(&env, "x <= y", &Domain::Nat).expect("cmp dispatch certifies");
        certify_monitor(&env, "x < y", &Domain::Machine(MachineUIntWidth::U64))
            .expect("machine cmp dispatch certifies");
    }

    #[test]
    fn integer_literals_elaborate_over_both_domains() {
        // A non-zero literal is in the supported fragment now (was "only 0"),
        // in both the unbounded Nat domain and a machine width. The elaborated
        // goal is well-typed and mentions the bound.
        let env = clean_kernel::Environment::with_prelude();
        let tc = clean_kernel::TypeChecker::new(&env);
        for (dom, ty) in [(Domain::Nat, "nat"), (Domain::Machine(MachineUIntWidth::U64), "u64")] {
            let goal = elaborate_goal_typed_with_facets("x < 10", &[("x", ty)], &FacetTable::new())
                .unwrap_or_else(|e| panic!("`x < 10` over {ty} must elaborate: {e}"));
            let _ =
                tc.infer_type(&goal).unwrap_or_else(|e| panic!("goal over {ty} well-typed: {e:?}"));
            // The `zero` special-case is untouched; a literal 0 still elaborates.
            let _ = elaborate_goal_typed_with_facets("x < 0", &[("x", ty)], &FacetTable::new())
                .unwrap_or_else(|e| panic!("`x < 0` over {ty} must still elaborate: {e}"));
            let _ = dom;
        }
    }

    #[test]
    fn machine_literal_out_of_range_fails_closed() {
        // A literal that does not fit the width is rejected — NOT silently
        // wrapped through `ofNat`'s mod-2^w (mirrors Rust's own "literal out of
        // range for `u8`"). 255 is the max u8 and elaborates; 256 does not.
        let ok = elaborate_goal_typed_with_facets("x <= 255", &[("x", "u8")], &FacetTable::new());
        assert!(ok.is_ok(), "255 is in range for u8: {ok:?}");
        let err = elaborate_goal_typed_with_facets("x <= 256", &[("x", "u8")], &FacetTable::new())
            .unwrap_err();
        assert!(err.contains("out of range for `u8`"), "{err}");
        // The Nat domain is unbounded — a large literal is fine there.
        let _ = elaborate_goal_typed_with_facets("x <= 256", &[("x", "nat")], &FacetTable::new())
            .expect("256 is fine over unbounded Nat");
    }

    #[test]
    fn certified_monitor_over_a_literal_bound() {
        // GOLD TEST: the kernel itself validates literal support. A certified
        // monitor for `x < 10` builds the kernel goal (`Nat.lt x 10` via the
        // literal node) AND the executable twin, and the Clean kernel checks the
        // `monitor = true ↔ P` equivalence — so a passing check is kernel
        // evidence the literal is sound, not merely structurally plausible.
        let env = clean_kernel::Environment::with_prelude();
        let tc = clean_kernel::TypeChecker::new(&env);
        for dom in [Domain::Nat, Domain::Machine(MachineUIntWidth::U64)] {
            let m = certify_monitor(&env, "x < 10", &dom)
                .unwrap_or_else(|e| panic!("`x < 10` monitor over {dom:?} must certify: {e}"));
            tc.check_type(&m.equivalence_proof, &m.equivalence_goal)
                .unwrap_or_else(|e| panic!("proof inhabits goal over {dom:?}: {e:?}"));
            // The executable twin respects the bound: 9 < 10 holds, 10 < 10 does not.
            let mon = m.into_runtime();
            assert!(mon.evaluate(&[("x", 9)]).expect("eval 9"), "9 < 10 must hold");
            assert!(!mon.evaluate(&[("x", 10)]).expect("eval 10"), "10 < 10 must not hold");
        }
    }

    #[test]
    fn subtraction_certifies_with_domain_semantics() {
        // `-` joins the term fragment. A monitor is a DECISION PROCEDURE, so
        // `x - y <= x` certifies over BOTH domains (the monitor faithfully
        // decides the proposition for every input) even though the proposition
        // itself is only universally true over Nat. The executable twin then
        // exposes the domain-specific semantics: truncated over Nat, wrapping
        // over the machine width.
        let env = clean_kernel::Environment::with_prelude();
        let tc = clean_kernel::TypeChecker::new(&env);

        // Nat: `Nat.sub` saturates at 0, so `x - y <= x` holds everywhere —
        // including when `y > x` (3 - 5 = 0 <= 3).
        let nat = certify_monitor(&env, "x - y <= x", &Domain::Nat)
            .expect("nat subtraction monitor must certify");
        tc.check_type(&nat.equivalence_proof, &nat.equivalence_goal)
            .expect("nat sub proof inhabits goal");
        let nat_mon = nat.into_runtime();
        assert!(nat_mon.evaluate(&[("x", 5), ("y", 3)]).expect("5-3"), "5-3=2 <= 5");
        assert!(
            nat_mon.evaluate(&[("x", 3), ("y", 5)]).expect("3-5"),
            "3-5 truncates to 0 <= 3 over Nat"
        );

        // u64: `UInt64.sub` WRAPS, so `x - y <= x` is FALSE at x=0, y=1
        // (0 - 1 = u64::MAX). The monitor still certifies (it decides that
        // correctly) and the executable twin reports false there.
        let u64d = Domain::Machine(MachineUIntWidth::U64);
        let mach = certify_monitor(&env, "x - y <= x", &u64d)
            .expect("u64 subtraction monitor must certify");
        tc.check_type(&mach.equivalence_proof, &mach.equivalence_goal)
            .expect("u64 sub proof inhabits goal");
        let mach_mon = mach.into_runtime();
        assert!(mach_mon.evaluate(&[("x", 5), ("y", 3)]).expect("5-3"), "5-3=2 <= 5");
        assert!(
            !mach_mon.evaluate(&[("x", 0), ("y", 1)]).expect("0-1"),
            "0-1 wraps to u64::MAX, which is not <= 0"
        );
    }

    #[test]
    fn disequality_certifies_via_not_eq_desugaring() {
        // `a != b` desugars to `!(a == b)`, so it certifies through the existing
        // Bool.not + equality certificate path over both domains, and the
        // executable twin decides it correctly.
        let env = clean_kernel::Environment::with_prelude();
        let tc = clean_kernel::TypeChecker::new(&env);
        for dom in [Domain::Nat, Domain::Machine(MachineUIntWidth::U64)] {
            let m = certify_monitor(&env, "x != y", &dom)
                .unwrap_or_else(|e| panic!("`x != y` over {dom:?} must certify: {e}"));
            tc.check_type(&m.equivalence_proof, &m.equivalence_goal)
                .unwrap_or_else(|e| panic!("proof inhabits goal over {dom:?}: {e:?}"));
            let mon = m.into_runtime();
            assert!(mon.evaluate(&[("x", 3), ("y", 5)]).expect("3 != 5"), "3 != 5 holds");
            assert!(!mon.evaluate(&[("x", 4), ("y", 4)]).expect("4 != 4"), "4 != 4 does not hold");
        }
        // `!=` also composes inside connectives and with a literal bound.
        certify_monitor(&env, "x != y && x < 10", &Domain::Machine(MachineUIntWidth::U64))
            .expect("`x != y && x < 10` must certify");
    }

    #[test]
    fn bool_clauses_elaborate_and_kernel_check() {
        // A `bool`-typed clause elaborates to a well-typed kernel goal. A bare
        // variable is read as `flag = true`; `==`/`!=`/`&&`/`||`/`!` and bool
        // literals compose. The kernel infers a type for each goal (it is a
        // well-formed Prop).
        let env = clean_kernel::Environment::with_prelude();
        let tc = clean_kernel::TypeChecker::new(&env);
        let cases: &[(&str, &[(&str, &str)])] = &[
            ("flag", &[("flag", "bool")]),
            ("!done", &[("done", "bool")]),
            ("a && b", &[("a", "bool"), ("b", "bool")]),
            ("a || !b", &[("a", "bool"), ("b", "bool")]),
            ("a == b", &[("a", "bool"), ("b", "bool")]),
            ("a != b", &[("a", "bool"), ("b", "bool")]),
            ("flag == true", &[("flag", "bool")]),
            ("true", &[]),
        ];
        for (spec, vt) in cases {
            let goal = elaborate_goal_typed(spec, vt)
                .unwrap_or_else(|e| panic!("bool clause `{spec}` must elaborate: {e}"));
            let _ = tc
                .infer_type(&goal)
                .unwrap_or_else(|e| panic!("bool goal `{spec}` must be well-typed: {e:?}"));
        }
    }

    #[test]
    fn bool_arithmetic_ordering_and_mixing_fail_closed() {
        // `bool` has no arithmetic or ordering, and a bool binding cannot share
        // a clause with an arithmetic one (that needs per-variable domains).
        let bb: &[(&str, &str)] = &[("a", "bool"), ("b", "bool")];
        assert!(elaborate_goal_typed("a + b == a", bb).is_err(), "no bool arithmetic");
        assert!(elaborate_goal_typed("a < b", bb).is_err(), "no bool ordering");
        // An integer literal is not a bool term.
        assert!(elaborate_goal_typed("flag == 1", &[("flag", "bool")]).is_err());
        // Mixing bool and an arithmetic domain WITHIN ONE comparison fails
        // closed (the operands must share a type); mixing ACROSS connectives is
        // fine and covered by `mixed_domains_across_connectives`.
        let err = elaborate_goal_typed("flag == x", &[("flag", "bool"), ("x", "u64")]).unwrap_err();
        assert!(err.contains("mixed domains in one comparison"), "{err}");
    }

    #[test]
    fn bool_equality_monitors_certify() {
        // GOLD: the Clean kernel certifies boolean-equality monitors through the
        // `decide (Eq Bool ·) + Bool.decEq` calculus (the machine-equality lane
        // with `Bool.decEq`), and the executable twin decides them.
        let env = clean_kernel::Environment::with_prelude();
        let tc = clean_kernel::TypeChecker::new(&env);

        // `a == b` over bool.
        let m = certify_monitor(&env, "a == b", &Domain::Bool)
            .expect("`a == b` over bool must certify");
        tc.check_type(&m.equivalence_proof, &m.equivalence_goal)
            .expect("bool eq proof inhabits goal");
        let mon = m.into_runtime();
        assert!(mon.evaluate(&[("a", 1), ("b", 1)]).expect("t==t"), "true == true");
        assert!(!mon.evaluate(&[("a", 1), ("b", 0)]).expect("t==f"), "true != false");

        // `flag == true` gives a bare bool an explicit certified monitor.
        let t = certify_monitor(&env, "flag == true", &Domain::Bool)
            .expect("`flag == true` must certify");
        tc.check_type(&t.equivalence_proof, &t.equivalence_goal).expect("flag==true proof");
        let tmon = t.into_runtime();
        assert!(tmon.evaluate(&[("flag", 1)]).expect("flag=t"), "flag==true holds at true");
        assert!(!tmon.evaluate(&[("flag", 0)]).expect("flag=f"), "flag==true fails at false");

        // `!=` and conjunction of bool equalities compose.
        certify_monitor(&env, "a != b", &Domain::Bool).expect("bool `!=` must certify");
        certify_monitor(&env, "a == b && c == d", &Domain::Bool)
            .expect("conjunction of bool equalities must certify");
    }

    #[test]
    fn bare_bool_monitors_certify_via_eq_true() {
        // A BARE boolean proposition (`flag`, not `flag == true`) now gets a
        // certified monitor: it decides as `flag == true` through the same Bool
        // equality lane, so no `false ≠ true` lemma is needed. Bare bools also
        // compose under the connectives, and the executable twin (where a bare
        // bool in prop position lowers to `Var == 1`) decides them.
        let env = clean_kernel::Environment::with_prelude();
        let tc = clean_kernel::TypeChecker::new(&env);

        let m = certify_monitor(&env, "flag", &Domain::Bool).expect("bare `flag` must certify");
        tc.check_type(&m.equivalence_proof, &m.equivalence_goal).expect("bare bool proof");
        let mon = m.into_runtime();
        assert!(mon.evaluate(&[("flag", 1)]).expect("t"), "flag holds when true");
        assert!(!mon.evaluate(&[("flag", 0)]).expect("f"), "flag fails when false");

        // Connectives over bare bools: `a && !b`.
        let comp = certify_monitor(&env, "a && !b", &Domain::Bool)
            .expect("`a && !b` over bare bools must certify");
        let cmon = comp.into_runtime();
        assert!(cmon.evaluate(&[("a", 1), ("b", 0)]).expect("t,f"), "true && !false");
        assert!(!cmon.evaluate(&[("a", 1), ("b", 1)]).expect("t,t"), "not (true && !true)");

        // The kernel goal still elaborates too.
        assert!(elaborate_goal_typed("flag", &[("flag", "bool")]).is_ok());
    }

    #[test]
    fn mixed_domain_monitors_certify() {
        // GOLD: a certified runtime monitor over a MIXED clause (`bool` + `u64`).
        // Each atom's certificate uses its own domain, the connective combines
        // them, and the executable twin normalizes each variable by its own
        // carrier.
        let env = clean_kernel::Environment::with_prelude();
        let tc = clean_kernel::TypeChecker::new(&env);

        let m = certify_monitor_typed(&env, "flag && x < 10", &[("flag", "bool"), ("x", "u64")])
            .expect("mixed bool+u64 monitor must certify");
        tc.check_type(&m.equivalence_proof, &m.equivalence_goal)
            .expect("mixed proof inhabits goal");
        let mon = m.into_runtime();
        assert!(mon.evaluate(&[("flag", 1), ("x", 3)]).expect("t,3"), "true && 3<10");
        assert!(!mon.evaluate(&[("flag", 0), ("x", 3)]).expect("f,3"), "false && _ is false");
        assert!(!mon.evaluate(&[("flag", 1), ("x", 10)]).expect("t,10"), "true && !(10<10)");

        // A three-way mix with equality and disequality across domains certifies.
        certify_monitor_typed(
            &env,
            "done || (n == 0 && b != c)",
            &[("done", "bool"), ("n", "nat"), ("b", "bool"), ("c", "bool")],
        )
        .expect("nat + bool mix across connectives must certify");
    }

    #[test]
    fn mixed_domain_monitor_with_arithmetic_uses_each_atom_domain() {
        // Arithmetic inherits its comparison atom's exact carrier even when a
        // connective combines that atom with a Bool proposition.
        let env = clean_kernel::Environment::with_prelude();
        let certified =
            certify_monitor_typed(&env, "flag && x + 1 < 10", &[("flag", "bool"), ("x", "u8")])
                .expect("mixed Bool/u8 arithmetic monitor must certify");
        let runtime = certified.into_runtime();
        assert!(runtime.evaluate(&[("flag", 1), ("x", 255)]).unwrap());
        assert!(!runtime.evaluate(&[("flag", 0), ("x", 255)]).unwrap());
        assert!(!runtime.evaluate(&[("flag", 1), ("x", 9)]).unwrap());
        assert!(
            elaborate_goal_typed("flag && x + 1 < 10", &[("flag", "bool"), ("x", "u8")]).is_ok()
        );
    }

    #[test]
    fn division_and_remainder_by_positive_literal_certify() {
        // `/` and `%` by a positive integer literal join the fragment over BOTH
        // Nat AND machine widths — the latter via the `toNat`/`ofNat` round-trip
        // through `Nat.div`/`Nat.mod`, so no `UInt<W>.div`/`mod` prelude constant
        // is needed. The kernel certifies the evenness pattern and a halving
        // bound in each domain, and the executable twin decides them.
        let env = clean_kernel::Environment::with_prelude();
        let tc = clean_kernel::TypeChecker::new(&env);
        for dom in [Domain::Nat, Domain::Machine(MachineUIntWidth::U64)] {
            // Evenness `x % 2 == 0`.
            let even = certify_monitor(&env, "x % 2 == 0", &dom)
                .unwrap_or_else(|e| panic!("`x % 2 == 0` over {dom:?} must certify: {e}"));
            tc.check_type(&even.equivalence_proof, &even.equivalence_goal)
                .unwrap_or_else(|e| panic!("even proof inhabits goal over {dom:?}: {e:?}"));
            let even_mon = even.into_runtime();
            assert!(even_mon.evaluate(&[("x", 4)]).expect("4%2"), "4 is even");
            assert!(!even_mon.evaluate(&[("x", 3)]).expect("3%2"), "3 is odd");

            // Halving `x / 2 <= x` (always true).
            let half = certify_monitor(&env, "x / 2 <= x", &dom)
                .unwrap_or_else(|e| panic!("`x / 2 <= x` over {dom:?} must certify: {e}"));
            tc.check_type(&half.equivalence_proof, &half.equivalence_goal)
                .unwrap_or_else(|e| panic!("half proof inhabits goal over {dom:?}: {e:?}"));
            let half_mon = half.into_runtime();
            assert!(half_mon.evaluate(&[("x", 7)]).expect("7/2"), "7/2=3 <= 7");
        }
    }

    #[test]
    fn machine_division_uses_the_nat_encoding_not_uint_div() {
        // A machine-width `/`/`%` elaborates through `Nat.div`/`Nat.mod` with a
        // `toNat`/`ofNat` round-trip — NOT a (nonexistent in the prelude)
        // `UInt64.div`/`mod`. Asserting the term structure pins the encoding.
        let goal =
            elaborate_goal_typed_with_facets("x % 2 == 0", &[("x", "u64")], &FacetTable::new())
                .expect("u64 modulo now elaborates via the Nat encoding");
        let dump = format!("{goal:?}");
        assert!(dump.contains("mod"), "uses Nat.mod: {dump}");
        assert!(
            dump.contains("toNat") && dump.contains("ofNat"),
            "round-trips through the carrier: {dump}"
        );
    }

    #[test]
    fn division_by_nonliteral_or_zero_fails_closed() {
        // A variable divisor, or a zero divisor, is rejected: the elaborator
        // cannot see a `divisor != 0` obligation and the executable monitor
        // must never divide by zero. (Checked over Nat so the positive-literal
        // gate — not the machine-width gate — is what fires.)
        let vt: &[(&str, &str)] = &[("x", "nat"), ("y", "nat")];
        let err =
            elaborate_goal_typed_with_facets("x / y == 0", vt, &FacetTable::new()).unwrap_err();
        assert!(err.contains("positive integer literal divisor"), "{err}");
        let err0 =
            elaborate_goal_typed_with_facets("x / 0 == 0", &[("x", "nat")], &FacetTable::new())
                .unwrap_err();
        assert!(err0.contains("positive integer literal divisor"), "{err0}");
        // Modulo by a variable likewise fails closed.
        assert!(elaborate_goal_typed_with_facets("x % y == 0", vt, &FacetTable::new()).is_err());
        // The Nat round-trip must not bypass Rust's typed-literal range gate.
        assert!(
            elaborate_goal_typed_with_facets("x / 300 == 0", &[("x", "u8")], &FacetTable::new(),)
                .is_err()
        );
    }

    #[test]
    fn bitwise_ops_certify() {
        // GOLD: `&`/`|`/`^` join the fragment — via `Nat.land`/`Nat.lor`/
        // `Nat.xor`, and over a machine width through the `toNat`/`ofNat`
        // round-trip. The kernel is the oracle for prelude support; the twin
        // decides the concrete bit-patterns.
        let env = clean_kernel::Environment::with_prelude();
        let tc = clean_kernel::TypeChecker::new(&env);
        for dom in [Domain::Nat, Domain::Machine(MachineUIntWidth::U64)] {
            // Low-bit mask: `x & 1 == 0` is evenness.
            let m = certify_monitor(&env, "x & 1 == 0", &dom)
                .unwrap_or_else(|e| panic!("`x & 1 == 0` over {dom:?} must certify: {e}"));
            tc.check_type(&m.equivalence_proof, &m.equivalence_goal)
                .unwrap_or_else(|e| panic!("proof over {dom:?}: {e:?}"));
            let mon = m.into_runtime();
            assert!(mon.evaluate(&[("x", 4)]).expect("4&1"), "4 & 1 == 0");
            assert!(!mon.evaluate(&[("x", 3)]).expect("3&1"), "3 & 1 != 0");

            // XOR self-inverse: `x ^ x == 0`.
            let xr = certify_monitor(&env, "x ^ x == 0", &dom)
                .unwrap_or_else(|e| panic!("`x ^ x == 0` over {dom:?} must certify: {e}"));
            assert!(xr.into_runtime().evaluate(&[("x", 7)]).expect("7^7"), "7 ^ 7 == 0");
        }
        // Bitwise-OR with a variable operand composes with `!=`.
        certify_monitor(&env, "(x | y) != 0", &Domain::Machine(MachineUIntWidth::U64))
            .expect("`(x | y) != 0` must certify");
    }

    #[test]
    fn bit_shifts_certify() {
        // `<<`/`>>` by a literal reduce to `* 2^n` / `/ 2^n`, reusing multiply /
        // divide (no shift prelude constant). The kernel is the oracle.
        let env = clean_kernel::Environment::with_prelude();
        let tc = clean_kernel::TypeChecker::new(&env);
        for dom in [Domain::Nat, Domain::Machine(MachineUIntWidth::U64)] {
            // Halving: `x >> 1 <= x`.
            let m = certify_monitor(&env, "x >> 1 <= x", &dom)
                .unwrap_or_else(|e| panic!("`x >> 1 <= x` over {dom:?} must certify: {e}"));
            tc.check_type(&m.equivalence_proof, &m.equivalence_goal)
                .unwrap_or_else(|e| panic!("proof over {dom:?}: {e:?}"));
            assert!(m.into_runtime().evaluate(&[("x", 7)]).expect("7>>1"), "7>>1 = 3 <= 7");

            // `x << 3` is `x * 8`: the twin decides `x << 3 == 0`.
            let sh = certify_monitor(&env, "x << 3 == 0", &dom)
                .unwrap_or_else(|e| panic!("`x << 3 == 0` over {dom:?} must certify: {e}"));
            let smon = sh.into_runtime();
            assert!(smon.evaluate(&[("x", 0)]).expect("0<<3"), "0 << 3 == 0");
            assert!(!smon.evaluate(&[("x", 1)]).expect("1<<3"), "1 << 3 = 8 != 0");
        }
        // An over-width shift fails closed for a machine width.
        assert!(elaborate_goal_typed("x << 64 == 0", &[("x", "u64")]).is_err());
        assert!(elaborate_goal_typed("x << 8 == 0", &[("x", "u8")]).is_err());

        // Nat shifts share the implementation's exact `< 64` power-of-two
        // fragment. In particular, a literal above `u32::MAX` must not narrow
        // modulo 2^32 and silently become a shift by zero.
        let huge_shift = "x << 4294967296 == 0";
        assert!(elaborate_goal_typed(huge_shift, &[("x", "nat")]).is_err());
        assert!(certify_monitor(&env, huge_shift, &Domain::Nat).is_err());

        // Exercise the executable lowering directly as well, so the runtime
        // twin cannot independently reintroduce the same lossy narrowing.
        let runtime_ast: SynExpr = syn::parse_str("x << 4294967296").expect("valid shift syntax");
        let runtime_domains = BTreeMap::from([("x".to_string(), Domain::Nat)]);
        assert!(runtime_monitor_term(&runtime_ast, &Domain::Nat, &runtime_domains).is_err());
    }

    #[test]
    fn certified_monitor_conjunction() {
        let env = clean_kernel::Environment::with_prelude();
        let tc = clean_kernel::TypeChecker::new(&env);
        // A conjunction of comparisons certifies as ONE monitor
        // (Bool.and mon_P mon_Q with a kernel-checked P ∧ Q soundness cert).
        for spec in ["x <= y && x <= z", "x < y && y <= z", "x <= y && x == y"] {
            let m = certify_monitor(&env, spec, &Domain::Nat)
                .unwrap_or_else(|e| panic!("`{spec}` conjunction monitor must certify: {e}"));
            let _ = tc
                .infer_type(&m.equivalence_goal)
                .unwrap_or_else(|e| panic!("`{spec}` goal well-typed: {e:?}"));
            tc.check_type(&m.equivalence_proof, &m.equivalence_goal)
                .unwrap_or_else(|e| panic!("`{spec}` proof inhabits goal: {e:?}"));
        }
        // Nested conjunction (right-associated) also certifies.
        certify_monitor(&env, "x <= y && y <= z && z <= w", &Domain::Nat)
            .expect("nested conjunction must certify");
        // Machine-domain conjunction of comparisons certifies (toNat order).
        certify_monitor(&env, "x < y && y < z", &Domain::Machine(MachineUIntWidth::U64))
            .expect("machine conjunction must certify");
    }

    #[test]
    fn certified_monitor_disjunction() {
        let env = clean_kernel::Environment::with_prelude();
        let tc = clean_kernel::TypeChecker::new(&env);
        // A disjunction of comparisons certifies as ONE monitor
        // (Bool.or mon_P mon_Q with a kernel-checked P ∨ Q soundness cert).
        for spec in ["x <= y || x <= z", "x < y || y < x", "x == y || x <= y"] {
            let m = certify_monitor(&env, spec, &Domain::Nat)
                .unwrap_or_else(|e| panic!("`{spec}` disjunction monitor must certify: {e}"));
            let _ = tc
                .infer_type(&m.equivalence_goal)
                .unwrap_or_else(|e| panic!("`{spec}` goal well-typed: {e:?}"));
            tc.check_type(&m.equivalence_proof, &m.equivalence_goal)
                .unwrap_or_else(|e| panic!("`{spec}` proof inhabits goal: {e:?}"));
        }
        // Mixed and/or (right-associated) and machine-domain disjunctions certify.
        certify_monitor(&env, "x <= y || y <= z && z <= w", &Domain::Nat)
            .expect("mixed and/or must certify");
        certify_monitor(&env, "x < y || y < z", &Domain::Machine(MachineUIntWidth::U64))
            .expect("machine disjunction must certify");
    }

    #[test]
    fn certified_monitor_negation() {
        let env = clean_kernel::Environment::with_prelude();
        let tc = clean_kernel::TypeChecker::new(&env);
        // Negated atomic clauses certify (mon = Bool.not mon_C, cert → ¬C via the
        // inner clause's completeness lemma).
        for spec in ["!(x <= y)", "!(x < y)", "!(x >= y)", "!(x == y)"] {
            let m = certify_monitor(&env, spec, &Domain::Nat)
                .unwrap_or_else(|e| panic!("`{spec}` negation monitor must certify: {e}"));
            let _ = tc
                .infer_type(&m.equivalence_goal)
                .unwrap_or_else(|e| panic!("`{spec}` goal well-typed: {e:?}"));
            tc.check_type(&m.equivalence_proof, &m.equivalence_goal)
                .unwrap_or_else(|e| panic!("`{spec}` proof inhabits goal: {e:?}"));
        }
        // Negated machine comparison certifies (toNat order completeness).
        certify_monitor(&env, "!(x < y)", &Domain::Machine(MachineUIntWidth::U64))
            .expect("machine negated comparison must certify");
        // Negated atomics compose inside && / ||.
        certify_monitor(&env, "!(x <= y) && x == z", &Domain::Nat)
            .expect("negated atomic inside && must certify");
        certify_monitor(&env, "!(x == y) || x <= z", &Domain::Nat)
            .expect("negated atomic inside || must certify");
    }

    #[test]
    fn certified_monitor_negation_of_compound() {
        let env = clean_kernel::Environment::with_prelude();
        let tc = clean_kernel::TypeChecker::new(&env);
        // With dual certificates, negation recurses through arbitrary structure:
        // De Morgan over &&/||, and double negation.
        for spec in [
            "!(x <= y && x <= z)", // ¬(P∧Q)
            "!(x <= y || x <= z)", // ¬(P∨Q)
            "!(!(x <= y))",        // ¬¬P
            "!(x <= y && x == z)", // mixed leaves
            "!(x <= y || y <= z && z <= w)",
        ] {
            let m = certify_monitor(&env, spec, &Domain::Nat)
                .unwrap_or_else(|e| panic!("`{spec}` compound-negation monitor must certify: {e}"));
            let _ = tc
                .infer_type(&m.equivalence_goal)
                .unwrap_or_else(|e| panic!("`{spec}` goal well-typed: {e:?}"));
            tc.check_type(&m.equivalence_proof, &m.equivalence_goal)
                .unwrap_or_else(|e| panic!("`{spec}` proof inhabits goal: {e:?}"));
        }
        // Machine domain: negated compound of comparisons still certifies.
        certify_monitor(&env, "!(x < y && y < z)", &Domain::Machine(MachineUIntWidth::U64))
            .expect("machine compound negation must certify");
    }

    #[test]
    fn certify_monitor_typed_requires_exact_closed_bindings() {
        let env = clean_kernel::Environment::with_prelude();
        let tc = clean_kernel::TypeChecker::new(&env);
        // u64-typed variables → machine domain, decided + certified end to end.
        let m = certify_monitor_typed(&env, "x <= y && x == y", &[("x", "u64"), ("y", "u64")])
            .expect("u64-typed clause must certify");
        tc.check_type(&m.equivalence_proof, &m.equivalence_goal).expect("proof inhabits goal");
        let _ = m.monitor();
        // Signed/`int`-spelled types are not closed supported carriers and
        // never silently coerce or default to Nat.
        assert!(certify_monitor_typed(&env, "!(x == y)", &[("x", "int"), ("y", "int")]).is_err());
        // Every occurring variable needs an explicit type; absence never
        // silently defaults a dropped u128/reference binding to Nat.
        assert!(certify_monitor_typed(&env, "x <= y", &[]).is_err());
        // Unrelated unsupported/signed/bool parameters do not poison the
        // clause's actual free-variable domain: the monitor gate accepts the
        // function's complete signature and binds only occurring variables.
        certify_monitor_typed(
            &env,
            "x == result",
            &[("x", "u64"), ("unused", "bool"), ("result", "u64")],
        )
        .expect("only occurring variables determine the monitor domain");
        // Mixed machine widths fail closed.
        assert!(certify_monitor_typed(&env, "x == y", &[("x", "u32"), ("y", "u64")]).is_err());
        // Nat is an exact logical carrier, not a wildcard that may be silently
        // reinterpreted as the clause's machine width.
        let mixed = certify_monitor_typed(&env, "x == n", &[("x", "u8"), ("n", "nat")])
            .expect_err("mixed Nat/machine monitor domains must fail closed");
        assert!(mixed.contains("mixed domains in one comparison"), "{mixed}");
        // Unknown type fails closed.
        assert!(certify_monitor_typed(&env, "x == y", &[("x", "String")]).is_err());
        // Duplicate bindings for an occurring variable fail closed rather
        // than resolving by first-match (same hardening as the exact typed
        // statement gate).
        assert!(
            certify_monitor_typed(&env, "x == y", &[("x", "u64"), ("x", "u64"), ("y", "u64")],)
                .is_err()
        );
        // Width-abstract USize is not executable until the compiler target is
        // kernel-bound; it remains honestly unmonitored.
        assert!(certify_monitor_typed(&env, "x == x", &[("x", "usize")]).is_err());
    }

    #[test]
    fn certified_runtime_payload_is_bound_and_wrapping() {
        let env = clean_kernel::Environment::with_prelude();
        let monitor = certify_monitor_typed(
            &env,
            "x + y == 0",
            &[("x", "u8"), ("y", "u8"), ("unused", "bool")],
        )
        .expect("u8 wrapping monitor certifies");
        assert_eq!(monitor.runtime.variables, ["x", "y"]);
        assert!(monitor.runtime.domains.values().all(|d| *d == RuntimeMonitorDomain::U8));
        assert!(monitor.runtime.evaluate(&[("x", 255), ("y", 1)]).unwrap());
        assert!(!monitor.runtime.evaluate(&[("x", 254), ("y", 1)]).unwrap());

        // The runtime consumer may neither invent nor ignore bindings.
        assert!(monitor.runtime.evaluate(&[("x", 255)]).is_err());
        assert!(monitor.runtime.evaluate(&[("x", 255), ("y", 1), ("z", 0)]).is_err());
        assert!(monitor.runtime.evaluate(&[("x", 255), ("x", 1)]).is_err());
        assert!(monitor.runtime.evaluate(&[("x", 256), ("y", 0)]).is_err());
    }

    #[test]
    fn closed_nat_monitor_has_an_exact_zero_argument_payload() {
        let env = clean_kernel::Environment::with_prelude();
        let monitor = certify_monitor_typed(&env, "0 == 0", &[])
            .expect("closed zero-only proposition must certify");
        assert!(monitor.runtime.variables.is_empty());
        assert!(monitor.runtime.domains.is_empty());
        assert!(monitor.runtime.evaluate(&[]).unwrap());

        let false_monitor = certify_monitor_typed(&env, "0 < 0", &[])
            .expect("closed false proposition still has an exact decision procedure");
        assert!(!false_monitor.runtime.evaluate(&[]).unwrap());
    }

    #[test]
    fn e6_call_in_spec_fails_closed_with_facet_diagnostic() {
        // E6 first brick: a program-fn call in a spec fails CLOSED with the
        // facet diagnostic (naming the E6 path), not the generic error.
        let err = elaborate_goal("min(x, y) <= x").unwrap_err();
        assert!(err.contains("sealed kernel admission"), "{err}");
        assert!(err.contains("Pure ∧ Total ∧ Deterministic ∧ NoPanic"), "{err}");
        assert!(err.contains("min"), "{err}");
        let err = elaborate_goal("x.len() <= y").unwrap_err();
        assert!(err.contains("facet"), "{err}");
        // The monitor lane inherits the same fail-closed behavior.
        let env = Environment::with_prelude();
        assert!(certify_monitor(&env, "min(x, y) <= x", &Domain::Nat).is_err());
    }

    #[test]
    fn structural_certificates_bridge_to_the_admission_facets() {
        // The compiler seam: four booleans from a structural `FacetSet` become
        // `FnFacets`. All-true is admissible (all Certified); any false is
        // Undetermined (a deeper lane may still establish it), so not admissible.
        let all = FnFacets::from_structural_certificates(true, true, true, true, "structural");
        assert!(all.admissible());
        let missing_nopanic =
            FnFacets::from_structural_certificates(true, false, true, true, "structural");
        assert!(!missing_nopanic.admissible());
        assert!(
            missing_nopanic.deficits().iter().any(|d| d.contains("not established")),
            "a false facet is Undetermined, not Unknown or Refuted: {:?}",
            missing_nopanic.deficits()
        );
    }

    #[test]
    fn from_structural_facets_builds_the_admission_table_and_still_fails_closed() {
        // The compiler glue in one call: `infer_facets` output (per-function
        // (total, no_panic, pure, deterministic) booleans) → a populated table.
        // `f` is all-four-true (admissible), `g` is not pure (undetermined).
        let table = FacetTable::from_structural_facets([
            ("crate::f", true, true, true, true),
            ("crate::g", true, true, false, true),
        ]);
        assert!(table.get("crate::f").is_some_and(FnFacets::admissible));
        assert!(table.get("crate::g").is_some_and(|fs| !fs.admissible()));

        // Certification is necessary but NOT sufficient: with no Admission minted
        // (the kernel-import step has not run), even the admissible `f` fails
        // closed — this is what keeps E6 sound until kernel import lands.
        assert_eq!(table.admitted("crate::f"), None);
        assert_eq!(table.admitted("crate::g"), None);

        // Once the kernel mints an Admission, the admissible `f` becomes
        // admitted; the non-admissible `g` stays closed even if an Admission is
        // (wrongly) minted for it — both gates are required.
        let mut table = table;
        table.admit("crate::f", Admission::reflected("f_def", 1));
        table.admit("crate::g", Admission::reflected("g_def", 1));
        assert_eq!(table.admitted("crate::f"), Some(&Admission::reflected("f_def", 1)));
        assert_eq!(
            table.admitted("crate::g"),
            None,
            "a non-admissible facet record cannot be admitted"
        );
    }

    /// I2: a Rust program function enters the Clean environment as a REFLECTED
    /// carrier, and the table can answer that question about a kernel constant
    /// by name — the query the island admitter needs in order to refuse one.
    #[test]
    fn a_minted_carrier_is_reflected_and_findable_by_kernel_constant() {
        let mut env = Environment::with_prelude();
        let adm = admit_constant_function(
            &mut env,
            "trust_import_crate__answer",
            42,
            MachineUIntWidth::U64,
        )
        .expect("a constant u64 function must admit");
        assert!(adm.status().is_reflected());
        assert!(
            adm.require_kernel_check().is_err(),
            "a reflected carrier never satisfies a kernel-check requirement"
        );

        let mut table =
            FacetTable::from_structural_facets([("crate::answer", true, true, true, true)]);
        table.admit("crate::answer", adm);
        // Found by the KERNEL CONSTANT, not the callee path — that is the
        // lookup the refusal site has available.
        assert!(
            table
                .kernel_const_status("trust_import_crate__answer")
                .is_some_and(KernelStatus::is_reflected),
            "the table must be able to say what a kernel constant was minted as"
        );
        assert_eq!(table.kernel_const_status("crate::answer"), None);
        assert_eq!(table.kernel_const_status("some_island_def"), None);

        // The reverse query must survive a facet regression: it is used to
        // REFUSE, so an invisible stale record would be silently acceptable.
        table.insert("crate::answer", FnFacets::unknown());
        assert_eq!(table.admitted("crate::answer"), None, "the forward query fails closed");
        assert!(
            table.kernel_const_status("trust_import_crate__answer").is_some(),
            "the refusal query stays visible"
        );
    }

    /// E6 expansion I0: the diagnostic lookup that names WHO holds a kernel
    /// constant answers every recorded path of that mint and nothing else, and
    /// is not gated on the facet record either.
    #[test]
    fn admission_paths_for_kernel_const_names_every_holder_and_only_them() {
        let mut table = FacetTable::new();
        table.admit("crate::a::b", Admission::reflected("trust_import_crate__a__b", 2));
        table.admit("b", Admission::reflected("trust_import_crate__a__b", 2));
        table.admit("crate::c", Admission::reflected("trust_import_crate__c", 2));
        assert_eq!(
            table.admission_paths_for_kernel_const("trust_import_crate__a__b"),
            vec!["b", "crate::a::b"]
        );
        assert_eq!(
            table.admission_paths_for_kernel_const("trust_import_crate__c"),
            vec!["crate::c"]
        );
        assert!(table.admission_paths_for_kernel_const("trust_import_crate__d").is_empty());
    }

    #[test]
    fn admit_constant_function_mints_a_kernel_checked_admission() {
        // `fn answer() -> u64 { 42 }`: the minimal E6 kernel-import. The kernel
        // must accept the defining equation and then KNOW the constant.
        let mut env = Environment::with_prelude();
        let adm = admit_constant_function(&mut env, "answer_def", 42, MachineUIntWidth::U64)
            .expect("a constant u64 function must admit");
        assert_eq!(
            adm,
            Admission::reflected("answer_def", 0).with_declared_signature(
                Some(Domain::Machine(MachineUIntWidth::U64)),
                Some(DeclaredCarriers::of_domains(&[], &Domain::Machine(MachineUIntWidth::U64))),
            )
        );

        // Fail closed BEFORE the kernel on an out-of-range literal.
        assert!(
            admit_constant_function(&mut env, "bad", 300, MachineUIntWidth::U8).is_err(),
            "300 does not fit u8"
        );

        // The kernel now holds `answer_def : UInt64 := 42`: the constant is known
        // and typechecks at its carrier (add_decl already FULL-KERNEL-CHECKED the
        // value against the type and recorded the equation — that acceptance is
        // the soundness guarantee this mint rests on).
        let tc = clean_kernel::TypeChecker::new(&env);
        let answer = Expr::const_(Name::from_string("answer_def"), vec![]);
        let uint64 = Expr::const_(Name::from_string("UInt64"), vec![]);
        tc.check_type(&answer, &uint64).expect("admitted constant typechecks at UInt64");
    }

    #[test]
    fn admit_select_function_mints_min_and_max() {
        let mut env = Environment::with_prelude();
        let u = Domain::Machine(MachineUIntWidth::U64);
        // fn min2(a, b) -> u64 { if a < b { a } else { b } }
        admit_select_function(
            &mut env,
            "min2_def",
            &[u.clone(), u.clone()],
            SelectCmp::Lt,
            0,
            1,
            0,
            1,
        )
        .expect("min2 must admit");
        // fn max2(a, b) -> u64 { if a < b { b } else { a } }
        admit_select_function(
            &mut env,
            "max2_def",
            &[u.clone(), u.clone()],
            SelectCmp::Lt,
            0,
            1,
            1,
            0,
        )
        .expect("max2 must admit");

        // Semantic validation by definitional reduction — the branch is actually
        // taken correctly for both orderings.
        let tc = clean_kernel::TypeChecker::new(&env);
        let n = |v: u64| u.numeral(u128::from(v)).unwrap();
        let app2 = |f: &str, a: u64, b: u64| {
            Expr::apps(Expr::const_(Name::from_string(f), vec![]), [n(a), n(b)])
        };
        assert!(tc.is_def_eq(&app2("min2_def", 3, 5), &n(3)), "min2(3,5) = 3");
        assert!(tc.is_def_eq(&app2("min2_def", 5, 3), &n(3)), "min2(5,3) = 3");
        assert!(tc.is_def_eq(&app2("max2_def", 3, 5), &n(5)), "max2(3,5) = 5");
        assert!(tc.is_def_eq(&app2("max2_def", 5, 3), &n(5)), "max2(5,3) = 5");
    }

    #[test]
    fn admit_select_literal_function_mints_kernel_checked_threshold_selects() {
        let mut env = Environment::with_prelude();
        let u = Domain::Machine(MachineUIntWidth::U64);
        // fn min10(a, b) -> u64 { if a < 10 { a } else { b } } — R2/C9's shape.
        admit_select_literal_function(
            &mut env,
            "min10_def",
            &[u.clone(), u.clone()],
            SelectCmp::Lt,
            0,
            10,
            0,
            1,
        )
        .expect("the threshold select must admit");
        // fn ifz(a, b) -> u64 { if a == 0 { b } else { a } } — gcd's guard shape.
        admit_select_literal_function(
            &mut env,
            "ifz_def",
            &[u.clone(), u.clone()],
            SelectCmp::Eq,
            0,
            0,
            1,
            0,
        )
        .expect("the zero-guard select must admit");
        // fn le5(a, b) -> u64 { if a <= 5 { a } else { b } }.
        admit_select_literal_function(
            &mut env,
            "le5_def",
            &[u.clone(), u.clone()],
            SelectCmp::Le,
            0,
            5,
            0,
            1,
        )
        .expect("the Le threshold select must admit");

        // The kernel knows the minted type.
        let tc = clean_kernel::TypeChecker::new(&env);
        let uint64 = || Expr::const_(Name::from_string("UInt64"), vec![]);
        let arrow = Expr::arrow(uint64(), Expr::arrow(uint64(), uint64()));
        tc.check_type(&Expr::const_(Name::from_string("min10_def"), vec![]), &arrow)
            .expect("min10_def typechecks as u64 -> u64 -> u64");

        // SEMANTIC validation by definitional reduction — the branch is taken
        // correctly on closed inputs, INCLUDING the boundary value, where a
        // Le-for-Lt (or off-by-one-literal) mistake would show.
        let n = |v: u64| u.numeral(u128::from(v)).unwrap();
        let app2 = |f: &str, a: u64, b: u64| {
            Expr::apps(Expr::const_(Name::from_string(f), vec![]), [n(a), n(b)])
        };
        assert!(tc.is_def_eq(&app2("min10_def", 3, 99), &n(3)), "min10(3,99) = 3");
        assert!(tc.is_def_eq(&app2("min10_def", 15, 99), &n(99)), "min10(15,99) = 99");
        assert!(tc.is_def_eq(&app2("min10_def", 10, 99), &n(99)), "min10(10,99) = 99 (boundary)");
        assert!(tc.is_def_eq(&app2("ifz_def", 0, 7), &n(7)), "ifz(0,7) = 7");
        assert!(tc.is_def_eq(&app2("ifz_def", 3, 7), &n(3)), "ifz(3,7) = 3");
        assert!(tc.is_def_eq(&app2("le5_def", 5, 9), &n(5)), "le5(5,9) = 5 (boundary)");
        assert!(tc.is_def_eq(&app2("le5_def", 6, 9), &n(9)), "le5(6,9) = 9");
    }

    #[test]
    fn admit_select_literal_function_fails_closed() {
        let mut env = Environment::with_prelude();
        let u64d = || Domain::Machine(MachineUIntWidth::U64);
        let u8d = || Domain::Machine(MachineUIntWidth::U8);

        // Out-of-range literal: range-checked BEFORE the kernel, fails closed.
        assert!(
            admit_select_literal_function(
                &mut env,
                "bad_range",
                &[u8d(), u8d()],
                SelectCmp::Lt,
                0,
                300,
                0,
                1,
            )
            .is_err(),
            "literal 300 does not fit u8"
        );
        // Out-of-range parameter index.
        assert!(
            admit_select_literal_function(
                &mut env,
                "bad_index",
                &[u64d(), u64d()],
                SelectCmp::Lt,
                2,
                10,
                0,
                1,
            )
            .is_err(),
            "parameter 2 of a 2-parameter function"
        );
        // Mixed parameter domains.
        assert!(
            admit_select_literal_function(
                &mut env,
                "bad_mixed",
                &[u64d(), u8d()],
                SelectCmp::Lt,
                0,
                10,
                0,
                1,
            )
            .is_err(),
            "select over mixed domains is unsupported"
        );
        // Non-machine domain.
        assert!(
            admit_select_literal_function(
                &mut env,
                "bad_domain",
                &[Domain::Nat, Domain::Nat],
                SelectCmp::Lt,
                0,
                10,
                0,
                1,
            )
            .is_err(),
            "select requires a machine-integer domain"
        );
        // None of the refusals left a constant behind.
        for name in ["bad_range", "bad_index", "bad_mixed", "bad_domain"] {
            assert!(
                env.get_const(&Name::from_string(name)).is_none(),
                "a refused mint must not leave `{name}` in the environment"
            );
        }
    }

    #[test]
    fn admit_expr_function_mints_a_semantically_correct_arithmetic_admission() {
        let mut env = Environment::with_prelude();
        let u = Domain::Machine(MachineUIntWidth::U64);
        // fn winc(x: u64) -> u64 { x.wrapping_add(1) }  (machine `+` is wrapping)
        let adm = admit_expr_function(&mut env, "winc_def", "x + 1", &["x"], &u)
            .expect("wrapping-add function must admit");
        assert_eq!(
            adm,
            Admission::reflected("winc_def", 1).with_declared_signature(
                Some(u.clone()),
                Some(DeclaredCarriers::of_domains(&[u.clone()], &u)),
            )
        );

        // fn add2(x, y) -> u64 { x + y } — a two-parameter arithmetic body.
        admit_expr_function(&mut env, "add2_def", "x + y", &["x", "y"], &u)
            .expect("two-arg add must admit");

        // SEMANTIC validation via definitional reduction: winc_def(41) ≡ 42 and
        // add2_def(20, 22) ≡ 42. A wrong encoding would typecheck but fail these.
        let tc = clean_kernel::TypeChecker::new(&env);
        let n = |v: u64| u.numeral(u128::from(v)).unwrap();
        let winc41 = Expr::app(Expr::const_(Name::from_string("winc_def"), vec![]), n(41));
        assert!(tc.is_def_eq(&winc41, &n(42)), "winc_def(41) must reduce to 42");
        let add2 = Expr::apps(Expr::const_(Name::from_string("add2_def"), vec![]), [n(20), n(22)]);
        assert!(tc.is_def_eq(&add2, &n(42)), "add2_def(20, 22) must reduce to 42");
    }

    #[test]
    fn admit_projection_function_mints_a_kernel_checked_admission() {
        let mut env = Environment::with_prelude();
        let u64d = || Domain::Machine(MachineUIntWidth::U64);
        // fn fst(x: u64, y: u64) -> u64 { x }  ⇒  fun x y => x  :  u64 → u64 → u64
        let adm = admit_projection_function(&mut env, "fst_def", &[u64d(), u64d()], 0)
            .expect("first-projection must admit");
        assert_eq!(
            adm,
            Admission::reflected("fst_def", 2).with_declared_signature(
                Some(u64d()),
                Some(DeclaredCarriers::of_domains(&[u64d(), u64d()], &u64d())),
            )
        );

        // Returning the SECOND parameter is equally sound (de Bruijn index 0).
        admit_projection_function(&mut env, "snd_def", &[u64d(), u64d()], 1)
            .expect("second-projection must admit");
        // Identity (arity 1).
        admit_projection_function(&mut env, "id_def", &[u64d()], 0).expect("identity must admit");

        // Out-of-range projection index fails closed.
        assert!(admit_projection_function(&mut env, "bad", &[u64d()], 5).is_err());

        // The kernel knows `fst_def : UInt64 → UInt64 → UInt64`.
        let tc = clean_kernel::TypeChecker::new(&env);
        let fst = Expr::const_(Name::from_string("fst_def"), vec![]);
        let u = || Expr::const_(Name::from_string("UInt64"), vec![]);
        let arrow = Expr::arrow(u(), Expr::arrow(u(), u()));
        tc.check_type(&fst, &arrow).expect("fst_def typechecks as u64 → u64 → u64");
    }

    /// C6 clause-path regression (e6 probes f06–f09): a VARIABLE-FREE ensures
    /// atom used to fall to the `Nat` default and mint `Eq Nat` over `UInt64`
    /// terms — ill-typed, so the defeq route rejected clauses whose two sides
    /// were definitionally equal. The atom's domain now comes from its TERMS:
    /// here, the admitted callees' recorded return domains.
    #[test]
    fn variable_free_atom_elaborates_at_the_admitted_callees_return_domain() {
        let mut env = Environment::with_prelude();
        let u64d = Domain::Machine(MachineUIntWidth::U64);
        // `fn answer() -> u64 { 42 }` (the probes' self-fn) and `cid`, a
        // one-parameter identity applied to a literal (probe f09's shape).
        admit_constant_function(&mut env, "answer_def", 42, MachineUIntWidth::U64)
            .expect("constant admits");
        admit_projection_function(&mut env, "cid_def", &[u64d.clone()], 0)
            .expect("identity admits");

        let cert = || FacetStatus::Certified { evidence: "test".into() };
        let admissible =
            || FnFacets { pure: cert(), total: cert(), deterministic: cert(), no_panic: cert() };
        let mut facets = FacetTable::new();
        facets.insert("answer", admissible());
        facets.admit(
            "answer",
            Admission::reflected("answer_def", 0).with_return_domain(u64d.clone()),
        );
        facets.insert("cid", admissible());
        facets.admit("cid", Admission::reflected("cid_def", 1).with_return_domain(u64d.clone()));

        // On a nullary function the `result` rewrite leaves NO free variable:
        // `result == cid(42)` becomes `answer() == cid(42)`.
        let goal = elaborate_ensures("result == cid(42)", &[], "answer", &facets)
            .expect("a variable-free machine atom must elaborate");

        // KERNEL-CHECKED, twice over: the goal must be a well-typed
        // proposition (`Eq UInt64 …`, not the old ill-typed `Eq Nat` over
        // UInt64 terms), and reflexivity must close it — both sides reduce to
        // `UInt64.ofNat 42`, which is exactly the probes' defeq route.
        let tc = clean_kernel::TypeChecker::new(&env);
        let _ = tc
            .infer_type(&goal)
            .expect("the machine-domain goal must be well-typed");
        let refl = Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]),
            [
                Expr::const_(Name::from_string("UInt64"), vec![]),
                Expr::const_(Name::from_string("answer_def"), vec![]),
            ],
        );
        tc.check_type(&refl, &goal).expect("Eq.refl must close the machine-domain goal");
    }

    /// The default is preserved: with NO term evidence the variable-free atom
    /// still elaborates over `Nat`, and an admission that records no return
    /// domain (exactly what the four `admit_*` mints produce) changes nothing
    /// — the fix derives, it does not guess.
    #[test]
    fn a_variable_free_atom_without_term_evidence_still_defaults_to_nat() {
        let env = Environment::with_prelude();
        let tc = clean_kernel::TypeChecker::new(&env);

        // No calls, no suffixes: byte-identical to the untyped Nat path.
        let goal = elaborate_goal_typed("2 < 3", &[]).expect("bare literal atom elaborates");
        let want = elaborate_goal("2 < 3").expect("the Nat path elaborates");
        assert!(tc.is_def_eq(&goal, &want), "no evidence keeps the Nat default");

        // An admitted callee whose admission records NO return domain: the
        // atom still elaborates at the default, minting `Eq Nat` over the
        // UInt64 constant, and the reflexivity candidate still fails
        // `check_type` — the exact pre-fix "defeq-rejected" symptom the e6
        // probes showed (`infer_type` alone runs infer-only and does not
        // check App arguments, so the refusal is check_type's).
        let mut env2 = Environment::with_prelude();
        admit_constant_function(&mut env2, "answer_def", 42, MachineUIntWidth::U64)
            .expect("constant admits");
        let cert = || FacetStatus::Certified { evidence: "test".into() };
        let mut facets = FacetTable::new();
        facets.insert(
            "answer",
            FnFacets { pure: cert(), total: cert(), deterministic: cert(), no_panic: cert() },
        );
        facets.admit("answer", Admission::reflected("answer_def", 0));
        let goal = elaborate_goal_typed_with_facets("answer() == 42", &[], &facets)
            .expect("elaboration itself is total over the admitted structure");
        let tc2 = clean_kernel::TypeChecker::new(&env2);
        let refl = Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]),
            [nat(), Expr::const_(Name::from_string("answer_def"), vec![])],
        );
        assert!(
            tc2.check_type(&refl, &goal).is_err(),
            "a domain-less admission must keep the pre-fix Nat default (the reflexivity \
             candidate stays refused by the kernel), not guess the machine domain"
        );
    }

    /// The wrong-domain controls: conflicting term evidence refuses instead of
    /// picking a side, and a contradictory typed literal refuses the same way.
    #[test]
    fn conflicting_term_domain_evidence_refuses() {
        let cert = || FacetStatus::Certified { evidence: "test".into() };
        let admissible =
            || FnFacets { pure: cert(), total: cert(), deterministic: cert(), no_panic: cert() };
        let mut facets = FacetTable::new();
        facets.insert("a64", admissible());
        facets.admit(
            "a64",
            Admission::reflected("a64_def", 0)
                .with_return_domain(Domain::Machine(MachineUIntWidth::U64)),
        );
        facets.insert("b32", admissible());
        facets.admit(
            "b32",
            Admission::reflected("b32_def", 0)
                .with_return_domain(Domain::Machine(MachineUIntWidth::U32)),
        );

        // Two admitted callees with different recorded return domains.
        let err = elaborate_goal_typed_with_facets("a64() == b32()", &[], &facets)
            .expect_err("a u64/u32 comparison must refuse");
        assert!(err.contains("mixed domains"), "unexpected diagnostic: {err}");

        // A typed literal contradicting the callee's recorded domain.
        let err = elaborate_goal_typed_with_facets("a64() == 42u32", &[], &facets)
            .expect_err("a u64 callee against a u32 literal must refuse");
        assert!(err.contains("mixed domains"), "unexpected diagnostic: {err}");
    }

    /// e6 probe f04's spelling at the elaborator: a BARE identifier naming an
    /// ambient-admitted ZERO-ARITY constant is a citation, not a clause
    /// variable — it elaborates to the admitted kernel constant (the same
    /// constant `c()` resolves to), the exact-binding gate does not demand a
    /// type for it, and its recorded return domain types the atom.
    #[test]
    fn a_bare_identifier_naming_a_nullary_admission_elaborates_to_its_constant() {
        let mut env = Environment::with_prelude();
        admit_constant_function(&mut env, "c_def", 42, MachineUIntWidth::U64)
            .expect("constant admits");
        let cert = || FacetStatus::Certified { evidence: "test".into() };
        let mut facets = FacetTable::new();
        facets.insert(
            "c",
            FnFacets { pure: cert(), total: cert(), deterministic: cert(), no_panic: cert() },
        );
        facets.admit(
            "c",
            Admission::reflected("c_def", 0)
                .with_return_domain(Domain::Machine(MachineUIntWidth::U64)),
        );

        let goal = elaborate_goal_typed_with_facets("c == 42", &[], &facets)
            .expect("a bare nullary citation must elaborate");
        // Same proposition as the CALLED spelling — one admission, one
        // constant, two surface spellings.
        let called = elaborate_goal_typed_with_facets("c() == 42", &[], &facets)
            .expect("the called spelling elaborates");
        let tc = clean_kernel::TypeChecker::new(&env);
        let _ = tc
            .infer_type(&goal)
            .expect("the bare-citation goal must be well-typed");
        assert!(
            tc.is_def_eq(&goal, &called),
            "bare and called spellings must elaborate to the same proposition"
        );
    }

    /// Precedence is fail-closed: a clause BINDING shadows a same-named
    /// admission, so an island definition can never change what an existing
    /// green clause means. `x` stays the ∀-bound variable even when an
    /// admitted constant `x` (:= 7) exists.
    #[test]
    fn a_clause_binding_shadows_a_same_named_nullary_admission() {
        let mut env = Environment::with_prelude();
        admit_constant_function(&mut env, "x_def", 7, MachineUIntWidth::U64)
            .expect("constant admits");
        let cert = || FacetStatus::Certified { evidence: "test".into() };
        let mut facets = FacetTable::new();
        facets.insert(
            "x",
            FnFacets { pure: cert(), total: cert(), deterministic: cert(), no_panic: cert() },
        );
        facets.admit(
            "x",
            Admission::reflected("x_def", 0)
                .with_return_domain(Domain::Machine(MachineUIntWidth::U64)),
        );

        let shadowed = elaborate_goal_typed_with_facets("x == 1", &[("x", "u64")], &facets)
            .expect("a bound variable must stay elaborable under a same-named admission");
        let plain = elaborate_goal_typed("x == 1", &[("x", "u64")])
            .expect("the no-facets elaboration is the reference");
        let tc = clean_kernel::TypeChecker::new(&env);
        assert!(
            tc.is_def_eq(&shadowed, &plain),
            "the binding must win: `x` is the ∀-bound variable, never the admitted \
             constant (x_def := 7 would make this `∀ x, 7 == 1`)"
        );
    }

    // -------------------------------------------------------------------
    // I0 — identifier shadowing (ref-self design §4.0)
    // -------------------------------------------------------------------

    /// The help line the compiler computes for a by-value struct parameter.
    /// The elaborator never invents one; it only appends what it was handed.
    const STRUCT_PARAM_HELP: &str = "`c: Cst` is a by-value struct parameter whose clause \
         binders are its scalar fields; options: (1) name a scalar field (`c.degree`); \
         (2) if you meant the island definition `c`, rename the parameter or the definition";

    /// A kernel-checked (island-definition) status, built through the sealed
    /// authority seam exactly as `admit_certified_island_definition` builds it.
    fn island_status() -> trust_symbols::KernelStatus {
        use trust_symbols::KernelAuthority as _;
        trust_symbols::CicKernelRecheck::held_by_kernel_recheck().kernel_checked(
            trust_symbols::TermDigest::of_bytes(b"i0-test-digest"),
            trust_symbols::AxiomClosure::audited([]),
        )
    }

    /// A table admitting `name` as a kernel-checked island definition.
    fn island_table(name: &str, arity: usize) -> FacetTable {
        let cert = || FacetStatus::Certified { evidence: "clean-island-kernel-definition".into() };
        let mut t = FacetTable::new();
        t.insert(
            name,
            FnFacets { pure: cert(), total: cert(), deterministic: cert(), no_panic: cert() },
        );
        t.admit(name, Admission::kernel_checked(name, arity, island_status()));
        t
    }

    /// PINS THE TRUE RESOLUTION ORDER, which the ref-self design asserts and
    /// this lane was asked to confirm: in `elab_term`'s Path arm the GOAL
    /// BINDER is consulted before the ambient admission, so a clause variable
    /// wins over a same-named `clean { def … }` island definition — with or
    /// without I0's shadow map.
    ///
    /// This is the property the capture below is NOT a counterexample to: the
    /// capture happens because a by-value struct / `&T` parameter contributes
    /// no binder of its own name, not because an island def outranks a binder.
    #[test]
    fn a_goal_binder_resolves_before_a_same_named_island_definition() {
        let mut env = Environment::with_prelude();
        admit_constant_function(&mut env, "c", 80, MachineUIntWidth::U64).expect("constant admits");
        let facets = island_table("c", 0).with_shadowed_idents([("c", STRUCT_PARAM_HELP)]);

        let bound = elaborate_goal_typed_with_facets("c == 1", &[("c", "u64")], &facets)
            .expect("a bound variable must stay elaborable under a same-named island definition");
        let plain = elaborate_goal_typed("c == 1", &[("c", "u64")])
            .expect("the no-facets elaboration is the reference");
        let tc = clean_kernel::TypeChecker::new(&env);
        assert!(
            tc.is_def_eq(&bound, &plain),
            "the binder must win: `c` is the ∀-bound variable, never the island constant \
             (`c := 80` would make this `∀ c, 80 == 1`)"
        );
    }

    /// THE DEFECT, pinned with the guard switched off. It is the ELABORATOR's
    /// negative control, not the lane's mutation control: it shows the map is
    /// what refuses the capture (empty map ⇒ capture returns), but it cannot
    /// fail if the compiler stops INSTALLING the map, and it pins the empty-map
    /// default as permissive — a future lane that makes the elaborator fail
    /// closed with no map must delete it. The compiler-level control is
    /// `tests/ui/trust/e9_signature_name_never_binds_an_admitted_item.rs`.
    ///
    /// A by-value struct parameter `c: Cst` contributes the rows `c.degree`,
    /// `c.coeff` and no bare `c`, so the compiler hands the elaborator a
    /// binding list without `c`; the bare `c` in the clause then falls through
    /// to the admission table and a same-named island definition answers.
    /// `c := 80`, so the certified goal reads `∀ result, result = 80` while the
    /// clause text says "the parameter".
    #[test]
    fn without_the_shadow_map_a_bare_signature_name_is_captured_by_an_island_definition() {
        let mut env = Environment::with_prelude();
        admit_constant_function(&mut env, "c", 80, MachineUIntWidth::U64).expect("constant admits");
        let facets = island_table("c", 0);

        let captured =
            elaborate_goal_typed_with_facets("result == c", &[("result", "u64")], &facets)
                .expect("today's behaviour: the unbound bare name resolves to the island constant");
        let literal = elaborate_goal_typed("result == 80", &[("result", "u64")])
            .expect("the literal reading is the reference");
        let tc = clean_kernel::TypeChecker::new(&env);
        assert!(
            tc.is_def_eq(&captured, &literal),
            "the captured goal must be the island definition's VALUE — that is what makes \
             this a capture and not a harmless alias"
        );
    }

    /// I0 POSITIVE: with the compiler's shadow map installed, the same clause
    /// is refused, and the refusal names the rule, the captured constant and
    /// the compiler-computed options (v7/D3).
    #[test]
    fn a_signature_bound_name_with_no_clause_binder_refuses_the_island_definition() {
        let facets = island_table("c", 0).with_shadowed_idents([("c", STRUCT_PARAM_HELP)]);
        let err = elaborate_goal_typed_with_facets("result == c", &[("result", "u64")], &facets)
            .expect_err("a signature-bound bare name must not resolve to an island definition");
        assert!(err.contains("a clause names VALUES"), "{err}");
        assert!(err.contains("`c`"), "{err}");
        assert!(err.contains("bound by this function's signature"), "{err}");
        assert!(err.contains("c.degree"), "the compiler's options must reach the author: {err}");
    }

    /// CLOSE NEGATIVE TWIN of the guard: the refusal must fire only where a
    /// capture was possible. A shadowed name with NO admission behind it keeps
    /// the ordinary exact-binding message it reports today, so I0 changes no
    /// diagnostic for the (common) case of a clause that simply names something
    /// it did not bind.
    #[test]
    fn a_shadowed_name_with_no_admission_keeps_its_ordinary_refusal() {
        let facets = FacetTable::new().with_shadowed_idents([("c", STRUCT_PARAM_HELP)]);
        let err = elaborate_goal_typed_with_facets("result == c", &[("result", "u64")], &facets)
            .expect_err("`c` is bound by nothing the elaborator knows");
        assert!(
            err.contains("not exact") || err.contains("unbound variable"),
            "the pre-I0 message must survive where there was nothing to capture: {err}"
        );
        assert!(
            !err.contains("a clause names VALUES"),
            "the capture refusal must not fire without an admission to capture: {err}"
        );
    }

    /// I0 BARE ARM, on the route that is actually LIVE after round 1. The
    /// island-definition half is already refused upstream of the elaborator by
    /// `admit_clause_island_definitions` (round-1 commit f1e392382ce), but a
    /// PROGRAM FUNCTION is admitted under its bare `spec_spellings` key with no
    /// parameter-name filter at all, so `pub fn cap() -> u32` beside
    /// `fn f(cap: C) -> u32 ensures result == cap` captures the bare name. The
    /// control is the same table without the map.
    #[test]
    fn a_signature_bound_name_refuses_a_bare_program_function_admission() {
        let unshadowed = admitted_table("cap", Admission::reflected("cap_def", 0));
        elaborate_goal_typed_with_facets("result == cap", &[("result", "u64")], &unshadowed)
            .expect("control: unshadowed, the bare program-function admission resolves");

        let guarded = admitted_table("cap", Admission::reflected("cap_def", 0))
            .with_shadowed_idents([("cap", STRUCT_PARAM_HELP)]);
        let err = elaborate_goal_typed_with_facets("result == cap", &[("result", "u64")], &guarded)
            .expect_err("a signature-bound bare name must not resolve to a program function");
        assert!(err.contains("a clause names VALUES"), "{err}");
        assert!(err.contains("cap_def"), "the captured constant must be named: {err}");
    }

    /// I0 CALL ARM: `limit(x)` with a parameter named `limit` is a call of that
    /// binding in Rust, so it must not resolve to a same-named island
    /// definition. The control is the same table without the map.
    #[test]
    fn a_call_of_a_signature_bound_name_refuses_a_same_named_island_definition() {
        let help = "parameter `limit: &u32` has no scalar reading in this lane; options: \
                    (1) pass the value by value; (2) rename the parameter or the definition";
        let admitted = island_table("limit", 1);
        let resolved = elaborate_goal_typed_with_facets(
            "result == limit(x)",
            &[("result", "u64"), ("x", "u64")],
            &admitted,
        );
        assert!(resolved.is_ok(), "control: unshadowed, the island call resolves: {resolved:?}");

        let guarded = admitted.with_shadowed_idents([("limit", help)]);
        let err = elaborate_goal_typed_with_facets(
            "result == limit(x)",
            &[("result", "u64"), ("x", "u64")],
            &guarded,
        )
        .expect_err("a call of a signature-bound name must not resolve to an island definition");
        assert!(err.contains("is a call of that binding in Rust"), "{err}");
        assert!(err.contains("rename the parameter"), "{err}");
    }

    /// The call guard is UNIFORM: a REFLECTED carrier (a Rust `fn` the
    /// compiler projected into the kernel) is refused under a shadowed
    /// spelling too. `tests/ui/trust/contract_inlined_call_scope_stays_closed.rs`
    /// records why for the native lane — with a `shadow_id: fn(u64) -> u64`
    /// parameter, expanding the module's `shadow_id` "would falsely turn the
    /// postcondition into `result == x`" — and the citing lane must not be
    /// looser than the native one about the same identifier.
    #[test]
    fn the_call_guard_refuses_a_shadowed_reflected_carrier_too() {
        let unshadowed = admitted_table("helper", Admission::reflected("helper_def", 1));
        elaborate_goal_typed_with_facets(
            "result == helper(x)",
            &[("result", "u64"), ("x", "u64")],
            &unshadowed,
        )
        .expect("control: unshadowed, the program-function call resolves");

        let guarded = admitted_table("helper", Admission::reflected("helper_def", 1))
            .with_shadowed_idents([("helper", "`helper: fn(u64) -> u64` has no scalar reading")]);
        let err = elaborate_goal_typed_with_facets(
            "result == helper(x)",
            &[("result", "u64"), ("x", "u64")],
            &guarded,
        )
        .expect_err("a call of a signature-bound name is a call of the binding, not the item");
        assert!(err.contains("is a call of that binding in Rust"), "{err}");
    }

    /// The uniform call guard's PRICE, measured rather than assumed: the
    /// compiler's self identity is [`self_fn_spelling`]`(def_path)`, the
    /// CANONICAL def-path `k::f`, and the shadow map holds the BARE names a
    /// signature binds — so `fn f(f: u64)` in crate `k` keeps its E9 discharge,
    /// and the guard costs the E9 lanes nothing. A caller that passes a BARE
    /// self spelling and shadows it does lose that elaboration, which is the
    /// fail-closed direction; exempting the self name unconditionally would
    /// reopen the bare capture for `fn f(f: Cst) ensures result == f` beside
    /// `clean { def f … }`.
    #[test]
    fn a_bare_self_spelling_that_a_parameter_shadows_refuses_while_the_canonical_one_does_not() {
        // The compiler's own spelling for `fn f` of crate `k`.
        assert_eq!(self_fn_spelling("k::f"), "k::f", "the E9 lanes key self by the def-path");

        let canonical = admitted_table("k::f", Admission::reflected("f_def", 2))
            .with_shadowed_idents([("f", "rename the parameter or the definition")]);
        elaborate_ensures("result == x", &[("f", "u64"), ("x", "u64")], "k::f", &canonical).expect(
            "a bare parameter name must not shadow the CANONICAL self spelling the E9 lanes use",
        );

        let bare = admitted_table("f", Admission::reflected("f_def", 2))
            .with_shadowed_idents([("f", "rename the parameter or the definition")]);
        let err = elaborate_ensures("result == x", &[("f", "u64"), ("x", "u64")], "f", &bare)
            .expect_err("a BARE self spelling a parameter shadows fails closed");
        assert!(err.contains("is a call of that binding in Rust"), "{err}");
        assert!(err.contains("rename the parameter"), "{err}");
    }

    // -------------------------------------------------------------------
    // ref-self I1 — the borrow-erased PARAMETER VIEW's two marks
    // -------------------------------------------------------------------

    /// The view of `impl Point { fn x_ref(&self) -> u32 { self.x } }` for
    /// `Point { x: u32, y: u32 }`: the import is the two-parameter projection
    /// `fun p0 p1 => p0` over the pointee's scalar field VALUES, recorded
    /// under the clause-side names `self.x`, `self.y` and marked as a view.
    fn view_table(env: &mut Environment, key: &str) -> FacetTable {
        let u32d = Domain::Machine(MachineUIntWidth::U32);
        let admission =
            admit_projection_function(env, "trust_import_k__Point__x_ref", &[u32d.clone(), u32d], 0)
                .expect("the view's projection mints")
                .with_param_names(vec!["self.x".to_string(), "self.y".to_string()])
                .with_view("frozen-shared-erased");
        admitted_table(key, admission)
    }

    /// The POSITIVE half: in its own function's `ensures`, the view import is
    /// exactly what `result` denotes, and the clause binds the pointee's
    /// fields by their dotted names with no elaborator change at all.
    #[test]
    fn a_view_import_denotes_result_in_its_own_ensures() {
        let mut env = Environment::with_prelude();
        let facets = view_table(&mut env, "k::Point::x_ref");
        let goal = elaborate_ensures(
            "result == self.x",
            &[("self.x", "u32"), ("self.y", "u32")],
            "k::Point::x_ref",
            &facets,
        )
        .expect("the self-call position is the one position a view import is for");
        let tc = clean_kernel::TypeChecker::new(&env);
        let _ = tc.infer_type(&goal).expect("the goal must be well-typed");
        assert!(
            goal.to_string().contains("trust_import_k__Point__x_ref"),
            "`result` must be the view's defining equation: {goal}"
        );
    }

    /// **THE REGRESSION TWIN for `FacetTable::admitted`.** The compiler never
    /// writes a certified `FnFacets` record for a `&self` function — its
    /// borrow-bearing body is exactly what `facet_inference` refuses — so a
    /// view import reaches `elaborate_ensures` through a table holding the
    /// ADMISSION ALONE. Every other test here builds its table with
    /// `admitted_table`, which inserts the record the compiler does not, and
    /// that is what hid the defect this test pins (adversarial review 1,
    /// blocking finding 1: "the increment's headline capability is dead").
    #[test]
    fn a_view_admission_with_no_facet_record_still_denotes_result() {
        let mut env = Environment::with_prelude();
        let u32d = Domain::Machine(MachineUIntWidth::U32);
        let admission =
            admit_projection_function(&mut env, "trust_import_k__Point__x_ref", &[u32d.clone(), u32d], 0)
                .expect("the view's projection mints")
                .with_param_names(vec!["self.x".to_string(), "self.y".to_string()])
                .with_view("frozen-shared-erased");
        // NO `insert` — this table holds no facet record at all, exactly like
        // the one the compiler hands the elaborator for a `&self` function.
        let mut facets = FacetTable::new();
        facets.admit("k::Point::x_ref", admission);
        assert!(facets.get("k::Point::x_ref").is_none(), "the premise: no record exists");
        let goal = elaborate_ensures(
            "result == self.x",
            &[("self.x", "u32"), ("self.y", "u32")],
            "k::Point::x_ref",
            &facets,
        )
        .expect("a view admission carries its own isolated certification");
        let tc = clean_kernel::TypeChecker::new(&env);
        let _ = tc.infer_type(&goal).expect("the goal must be well-typed");
    }

    /// The MUTATION CONTROL for the exemption above: an ORDINARY admission with
    /// no facet record still fails closed. The bypass is keyed on the view
    /// mark, not on "an admission exists".
    #[test]
    fn m_an_ordinary_admission_with_no_facet_record_still_fails_closed() {
        let mut facets = FacetTable::new();
        facets.admit("k::f", Admission::reflected("f_def", 1));
        let err = elaborate_ensures("result == x", &[("x", "u64")], "k::f", &facets)
            .expect_err("no record, no admission");
        assert!(err.contains(SELF_NOT_E6_ADMITTED_REFUSAL_HEAD), "{err}");
    }

    /// The NEGATIVE twin the mark exists for: another function's clause calling
    /// the view import. Its arity is the FLATTENED one, so `x_ref(a, b)` would
    /// elaborate against a signature no Rust caller can write — rustc does not
    /// type-check clause text, so nothing else catches it.
    #[test]
    fn n_a_view_import_is_not_callable_from_another_functions_clause() {
        let mut env = Environment::with_prelude();
        let facets = view_table(&mut env, "x_ref");
        let err = elaborate_ensures(
            "x_ref(a, b) == 1",
            &[("a", "u32"), ("b", "u32")],
            "k::other",
            &facets,
        )
        .expect_err("a view import must not be callable from a clause");
        assert!(err.contains("borrow-erased PARAMETER VIEW"), "{err}");
        assert!(err.contains("frozen-shared-erased"), "the marker must be named: {err}");
        assert!(err.contains("options:"), "v7/D3 requires options: {err}");
    }

    /// …and from a position with no self spelling at all (the bare goal
    /// elaborator), which is the fail-closed default.
    #[test]
    fn n_a_view_import_is_not_callable_where_no_self_spelling_is_installed() {
        let mut env = Environment::with_prelude();
        let facets = view_table(&mut env, "x_ref");
        let err = elaborate_goal_typed_with_facets(
            "x_ref(a, b) == 1",
            &[("a", "u32"), ("b", "u32")],
            &facets,
        )
        .expect_err("with no self key installed a view import is unnameable");
        assert!(err.contains("borrow-erased PARAMETER VIEW"), "{err}");
    }

    /// …and in the BARE position, structurally rather than incidentally. A view
    /// always has at least one binder today, so the `arity >= 1` bare-name
    /// refusal would catch this anyway; the two facts are coupled only by
    /// argument unless the mark itself refuses here.
    #[test]
    fn n_a_view_import_is_not_nameable_bare() {
        let mut env = Environment::with_prelude();
        let facets = view_table(&mut env, "x_ref");
        let err = elaborate_goal_typed_with_facets("x_ref == 1", &[("a", "u32")], &facets)
            .expect_err("a bare view name is unnameable");
        assert!(err.contains("borrow-erased PARAMETER VIEW"), "{err}");
    }

    /// THE MUTATION CONTROL for the mark. The SAME admission without
    /// `with_view` elaborates the same call — so what refuses above is the
    /// mark, not the arity, the carriers or the name.
    #[test]
    fn m_without_the_view_mark_the_same_call_elaborates() {
        let mut env = Environment::with_prelude();
        let u32d = Domain::Machine(MachineUIntWidth::U32);
        let admission = admit_projection_function(
            &mut env,
            "trust_import_k__Point__x_ref",
            &[u32d.clone(), u32d],
            0,
        )
        .expect("the projection mints")
        .with_param_names(vec!["self.x".to_string(), "self.y".to_string()]);
        assert!(!admission.is_self_result_only(), "the mark is opt-in");
        assert_eq!(admission.view(), None);
        let facets = admitted_table("x_ref", admission);
        elaborate_ensures("x_ref(a, b) == 1", &[("a", "u32"), ("b", "u32")], "k::other", &facets)
            .expect("an UNMARKED import of the same shape is callable");
    }

    /// `with_view` sets BOTH marks: there is no way to record a view that is
    /// still callable, which is what makes "does this goal rest on a view"
    /// decidable from the self admission alone.
    #[test]
    fn the_view_mark_implies_self_result_only() {
        let admission = Admission::reflected("c", 1).with_view("frozen-shared-erased");
        assert_eq!(admission.view(), Some("frozen-shared-erased"));
        assert!(admission.is_self_result_only());
    }

    /// A parametered admission cited bare keeps failing closed — its bare name
    /// is a function value, outside the term fragment — and the refusal names
    /// the fix (v7/D3). An unadmitted bare identifier still fails the
    /// exact-binding gate exactly as before.
    #[test]
    fn a_bare_reference_to_a_parametered_admission_fails_closed_with_the_fix() {
        let cert = || FacetStatus::Certified { evidence: "test".into() };
        let mut facets = FacetTable::new();
        facets.insert(
            "f",
            FnFacets { pure: cert(), total: cert(), deterministic: cert(), no_panic: cert() },
        );
        facets.admit(
            "f",
            Admission::reflected("f_def", 1)
                .with_return_domain(Domain::Machine(MachineUIntWidth::U64)),
        );

        let err = elaborate_goal_typed_with_facets("f == 1", &[], &facets)
            .expect_err("a bare arity-1 reference must refuse");
        assert!(err.contains("must be applied"), "the refusal must carry the fix: {err}");

        let err = elaborate_goal_typed_with_facets("y == 1", &[], &facets)
            .expect_err("an unadmitted bare identifier must still refuse");
        assert!(
            err.contains("not exact") && err.contains("y"),
            "the exact-binding gate must still name the unbound identifier: {err}"
        );
    }

    /// A SUFFIXED literal is domain evidence on its own — and an unsupported
    /// suffix fails closed with the fix rather than silently minting `Nat`.
    #[test]
    fn a_typed_literal_pins_the_variable_free_atoms_domain() {
        let env = Environment::with_prelude();
        let tc = clean_kernel::TypeChecker::new(&env);
        let goal = elaborate_goal_typed("42u64 == 42", &[]).expect("suffixed literal elaborates");
        let _ = tc
            .infer_type(&goal)
            .expect("the machine-domain goal must be well-typed");
        let want = elaborate_goal_in("42 == 42", &Domain::Machine(MachineUIntWidth::U64))
            .expect("explicit-domain path elaborates");
        assert!(tc.is_def_eq(&goal, &want), "the u64 suffix must select the UInt64 carrier");

        // `usize` names no width; refusing carries the fix (v7/D3).
        let err =
            elaborate_goal_typed("1usize == 1", &[]).expect_err("a widthless suffix must refuse");
        assert!(err.contains("unsupported literal suffix"), "unexpected diagnostic: {err}");
    }

    // E9 discharge criterion (design note 2026-07-15): `elaborate_ensures`
    // substitutes `result` with the E6-admitted self-function's defining equation
    // and ∀-closes over PARAMETERS only, so the goal is the postcondition a cited
    // theorem must prove — NOT the false `∀ result …, …` the ordinary elaborator
    // produces. Validated SEMANTICALLY: the constructed goal reduces (is_def_eq)
    // to the intended statement, and distinct predicates yield distinct goals.
    #[test]
    fn elaborate_ensures_substitutes_result_with_the_self_definition() {
        let mut env = Environment::with_prelude();
        let u64d = || Domain::Machine(MachineUIntWidth::U64);
        // `fn f(x: u64) -> u64 { x }` — E6-admitted as the identity projection,
        // so `result == f_def(x)` and `f_def x` reduces to `x`.
        admit_projection_function(&mut env, "f_def", &[u64d()], 0).expect("identity admits");

        let cert = || FacetStatus::Certified { evidence: "test".into() };
        let admissible =
            FnFacets { pure: cert(), total: cert(), deterministic: cert(), no_panic: cert() };
        let mut facets = FacetTable::new();
        facets.insert("f", admissible);
        facets.admit("f", Admission::reflected("f_def", 1));

        let params: &[(&str, &str)] = &[("x", "u64")];
        let tc = clean_kernel::TypeChecker::new(&env);

        // `ensures result >= x` ⇒ goal `∀ x, x ≤ f_def x` ≡ `∀ x, x ≤ x`.
        let goal_ge = elaborate_ensures("result >= x", params, "f", &facets)
            .expect("admitted self-fn ensures must elaborate");
        let want_ge = elaborate_goal_typed("x >= x", params).unwrap();
        assert!(
            tc.is_def_eq(&goal_ge, &want_ge),
            "result>=x with result:=f_def(x)=x must reduce to `x>=x`:\n{goal_ge:?}"
        );

        // Distinct predicate ⇒ distinct goal: `>` must NOT be def-eq to `>=`, so a
        // theorem proving `∀ x, x ≥ x` can never discharge `ensures result > x`.
        let goal_gt = elaborate_ensures("result > x", params, "f", &facets).unwrap();
        assert!(
            !tc.is_def_eq(&goal_gt, &want_ge),
            "a strict `>` postcondition must not conflate with `>=`"
        );

        // The `result`-universal statement the OLD path builds (∀ over result AND
        // x) is NOT what the VC needs; `elaborate_ensures` must differ from it.
        let result_universal =
            elaborate_goal_typed("result >= x", &[("result", "u64"), ("x", "u64")]).unwrap();
        assert!(
            !tc.is_def_eq(&goal_ge, &result_universal),
            "elaborate_ensures must bind result to f_def(x), not ∀-close over it"
        );

        // Fail closed: a function that is NOT E6-admitted has no kernel denotation
        // for `result`.
        assert!(
            elaborate_ensures("result >= x", params, "not_admitted", &facets)
                .unwrap_err()
                .contains("E6-admitted"),
            "un-admitted self-fn must fail closed"
        );
        // The diagnostic recogniser names exactly THAT refusal — and no other:
        // the citation sweep uses it to decide whether to explain which E6
        // facet or body shape kept the function out of the import.
        assert!(is_self_not_e6_admitted_refusal(
            &elaborate_ensures("result >= x", params, "not_admitted", &facets).unwrap_err()
        ));
        // Negative twin: a DIFFERENT fail-closed refusal of the same entry
        // point (an un-admitted CALLEE in a result-free clause) is not it.
        let callee_refusal =
            elaborate_ensures("not_admitted(x) >= x", params, "not_admitted", &facets).unwrap_err();
        assert!(!is_self_not_e6_admitted_refusal(&callee_refusal), "{callee_refusal}");

        // A clause that uses a SUBSET of the parameters elaborates over just
        // those (the exact-binding gate is satisfied on the used vars) — a
        // full-parameter function with a single-variable postcondition, or a
        // quantified clause, discharges.
        let two_params: &[(&str, &str)] = &[("x", "u64"), ("y", "u64")];
        let subset = elaborate_ensures("x >= x", two_params, "not_admitted", &facets)
            .expect("a clause over a subset of params must elaborate");
        assert!(
            tc.is_def_eq(&subset, &elaborate_goal_typed("x >= x", &[("x", "u64")]).unwrap()),
            "subset clause goal must bind only the variables it uses"
        );
        let quantified =
            elaborate_ensures("forall i: u64, i >= i", two_params, "not_admitted", &facets)
                .expect("a quantified clause using no params must elaborate");
        assert!(
            tc.is_def_eq(&quantified, &elaborate_goal_typed("forall i: u64, i >= i", &[]).unwrap()),
            "quantified clause binds only its bound var, no params"
        );

        // A RESULT-FREE clause is a ∀-params statement independent of the return
        // value: it elaborates WITHOUT the self-admission gate (arbitrary-body
        // functions get result-free discharge), and equals the plain typed goal.
        let free = elaborate_ensures("x >= x", params, "not_admitted", &facets)
            .expect("result-free clause must not require self admission");
        let plain = elaborate_goal_typed("x >= x", params).unwrap();
        assert!(
            tc.is_def_eq(&free, &plain),
            "result-free ensures goal must be the plain ∀-params statement"
        );
        // ...but a call inside a result-free clause is still gated on the
        // CALLEE's admission.
        assert!(
            elaborate_ensures("other(x) >= x", params, "not_admitted", &facets).is_err(),
            "un-admitted CALLEE inside a result-free clause must fail closed"
        );
    }

    #[test]
    fn upgrade_from_structural_is_monotonic_and_preserves_refuted() {
        // The wiring path: the per-body whitelist scan leaves `f`'s Pure
        // Undetermined (a call it cannot see through); the whole-crate
        // composition later certifies it. Upgrade promotes only that facet.
        let mut t = FacetTable::new();
        t.insert("f", FnFacets::from_structural_certificates(true, true, false, true, "base"));
        assert!(!t.get("f").unwrap().admissible(), "Pure starts Undetermined");
        // `g`'s Pure is REFUTED — composition must never override a refutation.
        let mut g = FnFacets::unknown();
        g.pure = FacetStatus::Refuted { reason: "reachable panic".into() };
        t.insert("g", g);

        t.upgrade_from_structural([
            ("f", true, true, true, true),
            ("g", true, true, true, true),
            ("h", true, true, true, true), // no record → ignored
        ]);
        assert!(t.get("f").unwrap().admissible(), "Undetermined Pure promoted to Certified");
        assert!(
            matches!(t.get("g").unwrap().pure, FacetStatus::Refuted { .. }),
            "a Refuted facet is never promoted by composition"
        );
        assert!(t.get("h").is_none(), "a missing record is not created");

        // Monotonic: a later pass reporting `false` never retracts a certificate
        // an earlier pass (or a consumer) already established.
        t.upgrade_from_structural([("f", false, false, false, false)]);
        assert!(t.get("f").unwrap().admissible(), "false never retracts");
    }

    #[test]
    fn e6_admission_gate_requires_both_certified_facets_and_a_minted_constant() {
        // E6 brick 4 data model: a function is ADMITTED (elaborable to a kernel
        // constant) only when BOTH (a) all four facets are certified AND (b) an
        // Admission has been minted by the kernel-import step. Every other
        // combination confers nothing (fail-closed).
        let cert = || FacetStatus::Certified { evidence: "test".into() };
        let admissible =
            FnFacets { pure: cert(), total: cert(), deterministic: cert(), no_panic: cert() };
        let mut partial = FnFacets::unknown();
        partial.pure = cert();
        partial.total = cert();
        partial.deterministic = cert();
        // no_panic stays Unknown -> not admissible

        let adm = || Admission::reflected("min2", 2);

        // (1) certified facets + minted admission -> admitted.
        let mut t = FacetTable::new();
        t.insert("min2", admissible.clone());
        t.admit("min2", adm());
        assert_eq!(t.admitted("min2"), Some(&adm()));

        // (2) certified facets but NO admission minted -> not admitted.
        let mut t = FacetTable::new();
        t.insert("min2", admissible.clone());
        assert_eq!(t.admitted("min2"), None);

        // (3) admission minted but facets NOT fully certified -> not admitted
        //     (a stale admission whose facets regressed cannot re-authorize).
        let mut t = FacetTable::new();
        t.insert("min2", partial);
        t.admit("min2", adm());
        assert_eq!(t.admitted("min2"), None);

        // (4) admission for a function with no facet record at all -> nothing.
        let mut t = FacetTable::new();
        t.admit("min2", adm());
        assert_eq!(t.admitted("min2"), None);

        // (5) eviction drops the admission (an ambiguous bare name cannot stay
        //     admitted).
        let mut t = FacetTable::new();
        t.insert("min2", admissible);
        t.admit("min2", adm());
        assert_eq!(t.admitted("min2"), Some(&adm()));
        t.remove("min2");
        assert_eq!(t.admitted("min2"), None);
    }

    #[test]
    fn e6_admitted_call_elaborates_to_its_kernel_constant() {
        // E6 brick 4 elaboration: an admitted call `min2(x, y)` elaborates to
        // the kernel constant `min2` applied to the elaborated arguments,
        // instead of failing closed. Non-admitted calls still fail closed.
        let cert = || FacetStatus::Certified { evidence: "test".into() };
        let admissible =
            FnFacets { pure: cert(), total: cert(), deterministic: cert(), no_panic: cert() };
        let vt: &[(&str, &str)] = &[("x", "u64"), ("y", "u64")];

        let mut t = FacetTable::new();
        t.insert("min2", admissible);
        t.admit("min2", Admission::reflected("min2", 2));

        // Admitted: elaborates (no error), and the elaborated goal mentions the
        // kernel constant `min2`.
        let goal = elaborate_goal_typed_with_facets("min2(x, y) <= x", vt, &t)
            .expect("admitted call must elaborate");
        assert!(
            format!("{goal:?}").contains("min2"),
            "goal must apply the kernel constant: {goal:?}"
        );

        // Arity mismatch fails closed even for an admitted callee. (Its free
        // vars are just {x}, so pass the matching binding set — otherwise the
        // exact-bijection check would fire before the arity check.)
        let err =
            elaborate_goal_typed_with_facets("min2(x) <= x", &[("x", "u64")], &t).unwrap_err();
        assert!(err.contains("arity"), "{err}");

        // A DIFFERENT, non-admitted callee still fails closed with the facet
        // diagnostic (the admission table only admits `min2`).
        let err = elaborate_goal_typed_with_facets("other(x, y) <= x", vt, &t).unwrap_err();
        assert!(err.contains("no diagnostic E6 facet record exists"), "{err}");

        // The ambient table does not leak: after the admitted elaboration, the
        // plain path still fails closed on the same call.
        let err = elaborate_goal("min2(x, y) <= x").unwrap_err();
        assert!(err.contains("facet"), "{err}");
    }

    /// A PROOF-only admission and the certified facet record that makes it
    /// live, for both controls. The admission is a **Clean declaration**
    /// (`Admission::kernel_checked`): §5(b) withholds CALL from a Clean `def`
    /// by not minting a `DefId` for it, and `CarrierEvidence::Total` is
    /// unconstructed at I3, so no Clean declaration is executable in this tree.
    fn proof_only_clean_def_table() -> FacetTable {
        let cert = || FacetStatus::Certified { evidence: "clean-island-kernel-definition".into() };
        let mut t = FacetTable::new();
        t.insert(
            "clean_min2",
            FnFacets { pure: cert(), total: cert(), deterministic: cert(), no_panic: cert() },
        );
        t.admit(
            "clean_min2",
            Admission::kernel_checked("clean_min2", 2, trust_symbols::KernelStatus::Elaborated),
        );
        t
    }

    /// I3 control (a): naming a PROOF-only symbol from a CALL context must be
    /// an ERROR, and the error must say "visible but not executable" — never
    /// "not found", because the symbol *is* found and *is* observable.
    #[test]
    fn i3_control_a_call_context_refuses_a_proof_only_symbol() {
        let vt: &[(&str, &str)] = &[("x", "u64"), ("y", "u64")];
        let t = proof_only_clean_def_table();
        let err = elaborate_goal_typed_in(
            trust_symbols::Capability::Call,
            "clean_min2(x, y) <= x",
            vt,
            &t,
        )
        .expect_err("a CALL-context path naming a proof-only symbol must be refused");
        assert!(err.contains("visible but not executable"), "{err}");
        assert!(!err.contains("not found"), "a proof-visible symbol is never 'not found': {err}");
        assert!(err.contains("clean_min2"), "the refusal must name the symbol: {err}");
        assert!(err.contains("options:"), "v7/D3: a refusal carries the fix with options: {err}");
    }

    /// I3 control (b): the SAME symbol named from a PROOF context must NOT
    /// error. This is the half that keeps the firewall a firewall rather than
    /// a wall.
    #[test]
    fn i3_control_b_proof_context_admits_the_same_proof_only_symbol() {
        let vt: &[(&str, &str)] = &[("x", "u64"), ("y", "u64")];
        let t = proof_only_clean_def_table();
        let goal = elaborate_goal_typed_with_facets("clean_min2(x, y) <= x", vt, &t)
            .expect("a PROOF-context path naming a proof-only symbol must elaborate");
        assert!(
            format!("{goal:?}").contains("clean_min2"),
            "the proof goal must apply the kernel constant: {goal:?}"
        );
    }

    /// The other half of "not refuse everything", one layer below the control
    /// pair: a REFLECTED Rust carrier is executable, so a CALL context names it
    /// happily. If this ever fails alongside control (a) passing, the fix has
    /// degenerated into refusing the whole call lane.
    #[test]
    fn i3_a_call_context_still_names_an_executable_symbol() {
        let cert = || FacetStatus::Certified { evidence: "test".into() };
        let vt: &[(&str, &str)] = &[("x", "u64"), ("y", "u64")];
        let mut t = FacetTable::new();
        t.insert(
            "min2",
            FnFacets { pure: cert(), total: cert(), deterministic: cert(), no_panic: cert() },
        );
        t.admit("min2", Admission::reflected("min2", 2));

        for use_site in [trust_symbols::Capability::Proof, trust_symbols::Capability::Call] {
            let goal =
                elaborate_goal_typed_in(use_site, "min2(x, y) <= x", vt, &t).unwrap_or_else(|e| {
                    panic!("a reflected Rust carrier is executable ({use_site:?}): {e}")
                });
            assert!(format!("{goal:?}").contains("min2"), "{goal:?}");
        }
    }

    /// The capability check runs BEFORE the arity check: a use site that may
    /// not name the symbol must not be told to fix its argument count.
    #[test]
    fn i3_capability_is_decided_before_arity() {
        let t = proof_only_clean_def_table();
        let err = elaborate_goal_typed_in(
            trust_symbols::Capability::Call,
            "clean_min2(x) <= x",
            &[("x", "u64")],
            &t,
        )
        .expect_err("refused");
        assert!(err.contains("visible but not executable"), "{err}");
        assert!(!err.contains("arity"), "a capability refusal must not mention arity: {err}");
    }

    /// The transitive tag reaches the seam: an admission restricted by a
    /// proof-only edge is refused in a CALL context, and the refusal names the
    /// BINDING EDGE rather than the symbol the author wrote.
    #[test]
    fn i3_a_transitively_restricted_admission_names_the_binding_edge() {
        use trust_symbols::{Capability, EffectiveCapability};
        let cert = || FacetStatus::Certified { evidence: "test".into() };
        let vt: &[(&str, &str)] = &[("x", "u64"), ("y", "u64")];
        let mut t = FacetTable::new();
        t.insert(
            "wrapper",
            FnFacets { pure: cert(), total: cert(), deterministic: cert(), no_panic: cert() },
        );
        t.admit(
            "wrapper",
            Admission::reflected("wrapper", 2).restrict(
                EffectiveCapability::Determined(Capability::Proof),
                Some("crate::secret"),
            ),
        );

        // PROOF still names it — the firewall did not delete the symbol.
        let observed = elaborate_goal_typed_in(Capability::Proof, "wrapper(x, y) <= x", vt, &t)
            .expect("PROOF observes the whole closure");
        assert!(format!("{observed:?}").contains("wrapper"), "{observed:?}");

        let err = elaborate_goal_typed_in(Capability::Call, "wrapper(x, y) <= x", vt, &t)
            .expect_err("CALL through a proof-only edge is refused");
        assert!(err.contains("visible but not executable"), "{err}");
        assert!(err.contains("transitively"), "{err}");
        assert!(err.contains("crate::secret"), "the binding edge must be named: {err}");
        assert!(!err.contains("not found"), "{err}");
    }

    /// An admission whose closure is `Unrecorded` is refused in a CALL context
    /// with the "refusal to guess" diagnostic — not with a claim that the
    /// symbol is proof-only, which would be a finding nobody made.
    #[test]
    fn i3_an_unrecorded_closure_refuses_without_asserting_a_finding() {
        use trust_symbols::{Capability, EffectiveCapability};
        let cert = || FacetStatus::Certified { evidence: "test".into() };
        let vt: &[(&str, &str)] = &[("x", "u64"), ("y", "u64")];
        let mut t = FacetTable::new();
        t.insert(
            "opaque",
            FnFacets { pure: cert(), total: cert(), deterministic: cert(), no_panic: cert() },
        );
        t.admit(
            "opaque",
            Admission::reflected("opaque", 2).restrict(EffectiveCapability::Unrecorded, None),
        );

        let observed = elaborate_goal_typed_in(Capability::Proof, "opaque(x, y) <= x", vt, &t)
            .expect("observation needs no closure at all");
        assert!(format!("{observed:?}").contains("opaque"), "{observed:?}");
        let err = elaborate_goal_typed_in(Capability::Call, "opaque(x, y) <= x", vt, &t)
            .expect_err("refused");
        assert!(err.contains("visible but not executable"), "{err}");
        assert!(err.contains("INCOMPLETE"), "{err}");
        assert!(err.contains("refusal to guess"), "{err}");
    }

    /// `restrict` is a MEET: it lowers, is idempotent, and can never raise a
    /// PROOF-only admission to CALL however it is called.
    #[test]
    fn i3_restrict_can_only_lower_a_capability() {
        use trust_symbols::{Capability, EffectiveCapability};
        let call = EffectiveCapability::Determined(Capability::Call);
        let proof = EffectiveCapability::Determined(Capability::Proof);

        let reflected = Admission::reflected("f", 1);
        assert_eq!(reflected.capability(), call);
        assert_eq!(reflected.clone().restrict(call, None).capability(), call, "no-op");
        assert_eq!(reflected.clone().restrict(proof, None).capability(), proof, "lowers");

        let clean = Admission::kernel_checked("g", 1, KernelStatus::Elaborated);
        assert_eq!(clean.capability(), proof);
        assert_eq!(
            clean.clone().restrict(call, None).capability(),
            proof,
            "a CALL closure may not promote a PROOF-only declaration"
        );
        // Idempotent, and order-independent.
        let once = reflected.clone().restrict(proof, None);
        assert_eq!(once.clone().restrict(proof, None).capability(), proof);
        assert_eq!(once.restrict(call, None).capability(), proof);
        // Unrecorded is absorbing here too.
        assert_eq!(
            Admission::reflected("h", 1)
                .restrict(EffectiveCapability::Unrecorded, None)
                .capability(),
            EffectiveCapability::Unrecorded
        );
    }

    /// The ambient use-site capability is scoped and restored: a CALL
    /// elaboration must not leak CALL into a later PROOF one, and a refusal
    /// mid-elaboration must not strand it.
    #[test]
    fn i3_the_use_site_capability_does_not_leak() {
        use trust_symbols::Capability;
        let t = proof_only_clean_def_table();
        let vt: &[(&str, &str)] = &[("x", "u64"), ("y", "u64")];
        assert_eq!(ambient_use_site(), Capability::Proof, "default is PROOF");
        let _ = elaborate_goal_typed_in(Capability::Call, "clean_min2(x, y) <= x", vt, &t)
            .expect_err("refused");
        assert_eq!(ambient_use_site(), Capability::Proof, "restored after a refusal");
        let later = elaborate_goal_typed_with_facets("clean_min2(x, y) <= x", vt, &t)
            .expect("a later PROOF elaboration is unaffected");
        assert!(format!("{later:?}").contains("clean_min2"), "{later:?}");
        assert_eq!(ambient_use_site(), Capability::Proof);
    }

    /// `elaborate_ensures` — the citation seam — is a PROOF position. A
    /// citation is an observation, so a proof-only symbol in the clause must
    /// reach the kernel goal rather than be refused.
    #[test]
    fn i3_the_ensures_citation_seam_is_a_proof_position() {
        let mut t = proof_only_clean_def_table();
        let cert = || FacetStatus::Certified { evidence: "test".into() };
        t.insert(
            "f",
            FnFacets { pure: cert(), total: cert(), deterministic: cert(), no_panic: cert() },
        );
        t.admit("f", Admission::reflected("f_def", 2));
        let goal =
            elaborate_ensures("result <= clean_min2(x, y)", &[("x", "u64"), ("y", "u64")], "f", &t)
                .expect("a citation observes a proof-only symbol without ceremony");
        assert!(format!("{goal:?}").contains("clean_min2"), "{goal:?}");
    }

    #[test]
    fn e6_facet_table_refines_the_call_diagnostic() {
        // The facet table refines WHICH diagnostic a spec call gets, while
        // every production path stays closed because no sealed, item-bound
        // kernel admission exists.
        let vt: &[(&str, &str)] = &[("x", "u64"), ("y", "u64")];

        // (1) No record at all -> "no diagnostic E6 facet record exists".
        let t = FacetTable::new();
        let err = elaborate_goal_typed_with_facets("min(x, y) <= x", vt, &t).unwrap_err();
        assert!(err.contains("no diagnostic E6 facet record exists"), "{err}");
        assert!(err.contains("no sealed, item-bound kernel admission exists"), "{err}");

        // (2) Partial record -> names exactly the deficient facets.
        let mut t = FacetTable::new();
        let mut f = FnFacets::unknown();
        f.no_panic = FacetStatus::Certified { evidence: "l0-aggregate".into() };
        f.total = FacetStatus::Refuted { reason: "no decreases measure".into() };
        t.insert("min", f);
        let err = elaborate_goal_typed_with_facets("min(x, y) <= x", vt, &t).unwrap_err();
        assert!(err.contains("Pure (not established: no diagnostic finding)"), "{err}");
        assert!(err.contains("Total (refuted: no decreases measure)"), "{err}");
        assert!(err.contains("Deterministic (not established: no diagnostic finding)"), "{err}");
        assert!(!err.contains("NoPanic"), "positive finding must not be listed: {err}");
        assert!(err.contains("public facet findings are diagnostic only"), "{err}");
        assert!(err.contains("no sealed, item-bound kernel admission exists"), "{err}");
        assert!(
            !err.contains("all four public E6 structural facet findings"),
            "a partial record must never receive the all-positive diagnostic: {err}"
        );

        // (3) Fully established -> still fails closed, naming the sealed gate.
        let mut t = FacetTable::new();
        let cert = || FacetStatus::Certified { evidence: "test".into() };
        t.insert(
            "min",
            FnFacets { pure: cert(), total: cert(), deterministic: cert(), no_panic: cert() },
        );
        let err = elaborate_goal_typed_with_facets("min(x, y) <= x", vt, &t).unwrap_err();
        assert!(err.contains("public E6 structural facet findings"), "{err}");
        assert!(err.contains("diagnostic only"), "{err}");
        assert!(err.contains("no sealed, item-bound kernel admission exists"), "{err}");

        // (4) Calls nested under connectives/comparisons are still caught.
        let err = elaborate_goal_typed_with_facets("x <= y && min(x, y) <= x", vt, &t).unwrap_err();
        assert!(err.contains("diagnostic only"), "{err}");
        assert!(err.contains("no sealed, item-bound kernel admission exists"), "{err}");

        // (5) Method calls: unconditional fail-closed (no keying yet).
        let err = elaborate_goal_typed_with_facets("x.count() <= y", vt, &t).unwrap_err();
        assert!(err.contains("resolved item identity"), "{err}");
        assert!(err.contains("sealed, item-bound kernel admission are absent"), "{err}");

        // (6) Call-free specs elaborate identically to the plain entry point.
        let a = elaborate_goal_typed_with_facets("x <= y", vt, &t).unwrap();
        let b = elaborate_goal_typed("x <= y", vt).unwrap();
        assert_eq!(a, b);
    }

    #[test]
    fn monitor_out_of_fragment_fails_closed() {
        let env = clean_kernel::Environment::with_prelude();
        // Non-relational binary ops are not propositions.
        assert!(certify_monitor(&env, "x + y", &Domain::Nat).is_err());
        // A bare identifier is neither a comparison, equality, nor connective.
        assert!(certify_monitor(&env, "x", &Domain::Nat).is_err());
        // `!` of a non-proposition operand propagates the leaf failure.
        assert!(certify_monitor(&env, "!(x + y)", &Domain::Nat).is_err());
        // (Non-zero literals ARE in the fragment now — a monitor over a literal
        // bound certifies; see `certified_monitor_over_a_literal_bound`.)
    }

    #[test]
    fn machine_contract_elaborates() {
        // A u64 requires/ensures contract elaborates over UInt64 and is a
        // well-typed Prop the kernel can infer without error.
        let goal =
            elaborate_contract_in("x <= y", "x <= y", &Domain::Machine(MachineUIntWidth::U64))
                .expect("u64 contract must elaborate");
        let env = clean_kernel::Environment::with_prelude();
        let tc = clean_kernel::TypeChecker::new(&env);
        let _ = tc.infer_type(&goal).expect("machine contract must be well-typed");
        // Distinct from the Nat contract.
        let nat_goal = elaborate_contract("x <= y", "x <= y").unwrap();
        assert_ne!(goal, nat_goal);
    }

    #[test]
    fn mixed_width_fails_closed() {
        assert!(elaborate_goal_typed("x == y", &[("x", "u32"), ("y", "u64")]).is_err());
    }

    #[test]
    fn machine_contract_is_a_well_typed_distinct_wrapping_statement() {
        let domain = Domain::Machine(MachineUIntWidth::U64);
        let goal = elaborate_contract_in("x <= y", "x + 0 == x", &domain)
            .expect("u64 contract statement must elaborate");
        let env = clean_kernel::Environment::with_prelude();
        let _ = clean_kernel::TypeChecker::new(&env)
            .infer_type(&goal)
            .expect("machine contract statement must be well-typed");

        let nat_goal = elaborate_contract("x <= y", "x + 0 == x").unwrap();
        assert_ne!(goal, nat_goal, "machine wrapping and Nat statements must differ");
    }

    #[test]
    fn unsupported_type_fails_closed() {
        assert!(elaborate_goal_typed("x == x", &[("x", "String")]).is_err());
        assert!(elaborate_goal_typed("x == x", &[("x", "usize")]).is_err());
        assert!(elaborate_goal_typed("x == x", &[("x", "u256")]).is_err());
        // The newly bound wide/signed carriers are genuinely supported.
        assert!(elaborate_goal_typed("x == x", &[("x", "u128")]).is_ok());
        assert!(elaborate_goal_typed("x == x", &[("x", "i64")]).is_ok());
    }

    #[test]
    fn binding_names_are_an_exact_bijection() {
        assert!(elaborate_goal_typed("x == x", &[]).unwrap_err().contains("missing: [x]"));
        assert!(
            elaborate_goal_typed("x == x", &[("wrong", "u64")])
                .unwrap_err()
                .contains("missing: [x]; extra: [wrong]")
        );
        assert!(
            elaborate_goal_typed("x == x", &[("x", "u64"), ("unused", "u64")])
                .unwrap_err()
                .contains("extra: [unused]")
        );
        assert!(
            elaborate_goal_typed("x == x", &[("x", "u64"), ("x", "u64")])
                .unwrap_err()
                .contains("duplicate clause variable binding `x`")
        );
    }

    #[test]
    fn nat_is_not_a_machine_domain_wildcard() {
        // `x == n` mixes `u32` and `nat` in ONE comparison — the operands of a
        // single comparison must share a type, so it fails closed. (Mixing
        // ACROSS connectives is fine; see `mixed_domains_across_connectives`.)
        let error = elaborate_goal_typed("x == n", &[("x", "u32"), ("n", "nat")])
            .expect_err("mixed domains in one comparison must fail closed");
        assert!(error.contains("mixed domains in one comparison"), "{error}");
    }

    #[test]
    fn mixed_domains_across_connectives() {
        // Distinct variables may carry different domains: a connective combines
        // atoms of different domains (`bool` and `u64`), each elaborated over
        // its own carrier, into one well-typed kernel goal.
        let env = clean_kernel::Environment::with_prelude();
        let tc = clean_kernel::TypeChecker::new(&env);
        let goal =
            elaborate_goal_typed("flag == true && x < 10", &[("flag", "bool"), ("x", "u64")])
                .expect("bool + u64 across `&&` must elaborate");
        let _ = tc.infer_type(&goal).expect("mixed-domain goal is well-typed");
        // The binders carry each variable's own type — `Bool` and `UInt64` both
        // appear.
        let dump = format!("{goal:?}");
        assert!(dump.contains("Bool") && dump.contains("UInt64"), "{dump}");
        // A three-way mix also elaborates and kernel-checks.
        let g2 = elaborate_goal_typed(
            "done || (n < 3 && b == b)",
            &[("done", "bool"), ("n", "nat"), ("b", "bool")],
        )
        .expect("nat + bool mix across connectives elaborates");
        let _ = tc.infer_type(&g2).expect("three-way mixed goal well-typed");
    }

    #[test]
    fn closed_statement_rejects_extra_bindings() {
        assert!(elaborate_goal_typed("0 == 0", &[]).is_ok());
        assert!(elaborate_goal_typed("0 == 0", &[("ghost", "u64")]).is_err());
    }

    #[test]
    fn nat_valid_machine_wrap_claim_is_modeled_not_reused() {
        // `x + 1 > x` is true over Nat but FALSE at the maximum u32 value.
        // Now that nonzero literals and their exact wrapping semantics ARE
        // represented, the claim elaborates over u32 — but to the WRAPPING
        // encoding (`UInt32.add` under `UInt32.toNat`), which is a genuinely
        // different, and at `u32::MAX` false, statement. It is NOT the bare
        // `Nat.add` theorem, so a Nat proof cannot be accidentally reused: the
        // soundness the old fail-closed guarded is now enforced by faithful
        // modeling rather than by refusing to elaborate.
        // (`Name` renders in Debug as nested segments, so the wrapping encoding
        // shows as the presence of the `UInt32` carrier, its `toNat` coercion,
        // and the `ofNat` literal — all ABSENT from the bare-Nat statement.)
        let u32_goal = elaborate_goal_typed("x + 1 > x", &[("x", "u32")])
            .expect("wrap claim elaborates once literals are supported");
        let u32_dump = format!("{u32_goal:?}");
        assert!(u32_dump.contains("UInt32"), "u32 goal is over the machine carrier: {u32_dump}");
        assert!(u32_dump.contains("toNat"), "u32 compares through the toNat coercion: {u32_dump}");
        assert!(
            u32_dump.contains("ofNat"),
            "the literal went through the machine numeral: {u32_dump}"
        );

        // The Nat version is a DIFFERENT statement: no machine carrier, no
        // `toNat` coercion, no `ofNat`. Same surface syntax, distinct
        // denotation — the wrap claim can never borrow the Nat theorem's proof.
        let nat_goal = elaborate_goal_typed("x + 1 > x", &[("x", "nat")])
            .expect("Nat wrap-free claim elaborates");
        let nat_dump = format!("{nat_goal:?}");
        assert!(!nat_dump.contains("UInt32"), "nat goal has no machine carrier: {nat_dump}");
        assert!(!nat_dump.contains("toNat"), "nat needs no toNat coercion: {nat_dump}");
        assert!(!nat_dump.contains("ofNat"), "nat literal is a bare Nat node: {nat_dump}");
        assert_ne!(u32_dump, nat_dump, "the two domains must denote different statements");
    }

    /// The SIGNED-CONSTANT mint, and the one property that makes it worth
    /// anything: the body it stores is SYNTACTICALLY the term `elab_term`
    /// builds for the same literal at the same width — `Domain::zero` at `0`,
    /// `Domain::numeral` above it, `Domain::negative_numeral` below. An
    /// `is_def_eq` check would pass even if the mint picked `numeral(0)`;
    /// structural equality is what pins the SPELLING, which is what lets a
    /// clause mentioning the constant close by `Eq.refl`.
    #[test]
    fn admit_signed_constant_function_spells_literals_exactly_as_a_clause_does() {
        let mut env = Environment::with_prelude();
        let stored = |env: &Environment, name: &str| {
            env.get_const(&Name::from_string(name))
                .and_then(|c| c.value.clone())
                .unwrap_or_else(|| panic!("{name} must be a definition with a value"))
        };

        for (name, value, width) in [
            ("z64", 0i128, MachineSIntWidth::I64),
            ("o64", 1, MachineSIntWidth::I64),
            ("n64", -1, MachineSIntWidth::I64),
            ("min64", i128::from(i64::MIN), MachineSIntWidth::I64),
            ("max64", i128::from(i64::MAX), MachineSIntWidth::I64),
            ("z128", 0, MachineSIntWidth::I128),
            ("min128", i128::MIN, MachineSIntWidth::I128),
            ("max128", i128::MAX, MachineSIntWidth::I128),
            ("n8", -128, MachineSIntWidth::I8),
        ] {
            let d = Domain::Signed(width);
            let adm = admit_signed_constant_function(&mut env, name, value, width)
                .unwrap_or_else(|e| panic!("{name} must admit: {e}"));
            assert_eq!(adm.arity, 0);
            assert_eq!(adm.return_domain().cloned(), Some(d.clone()));
            let expected = if value == 0 {
                d.zero()
            } else if value > 0 {
                d.numeral(value.unsigned_abs()).expect("in range")
            } else {
                d.negative_numeral(value.unsigned_abs()).expect("in range")
            };
            assert_eq!(
                stored(&env, name),
                expected,
                "{name} must be spelled exactly as a clause spells {value}"
            );
            // …and the kernel really holds it at the two's-complement carrier.
            let tc = clean_kernel::TypeChecker::new(&env);
            tc.check_type(&Expr::const_(Name::from_string(name), vec![]), &d.ty())
                .unwrap_or_else(|e| panic!("{name} must typecheck at its carrier: {e:?}"));
        }

        // `0` takes `zero()`, NOT `numeral(0)` — the two differ structurally
        // (`Nat.zero` vs a `Nat` literal node), and the clause lane emits the
        // former. This is the row that would silently drift.
        assert_ne!(
            Domain::Signed(MachineSIntWidth::I64).zero(),
            Domain::Signed(MachineSIntWidth::I64).numeral(0).expect("0 is in range"),
            "the two zero spellings are structurally distinct, so the choice matters"
        );

        // Out of range fails closed BEFORE the kernel, at every width.
        for (value, width) in [
            (128i128, MachineSIntWidth::I8),
            (-129, MachineSIntWidth::I8),
            (i128::from(i64::MAX) + 1, MachineSIntWidth::I64),
            (i128::from(i64::MIN) - 1, MachineSIntWidth::I64),
        ] {
            assert!(
                admit_signed_constant_function(&mut env, "parked", value, width).is_err(),
                "{value} must fail closed at {width:?}"
            );
        }
    }

    /// The SIGN-EXTENSION model is the composition of the checked lane's
    /// exact-`Int` bridge, in that order and at those widths — `ofInt` at the
    /// TARGET width applied to `toInt` at the SOURCE width — and a narrowing
    /// request is refused rather than named `sext`.
    #[test]
    fn seed_sext_model_composes_the_exact_int_bridge_and_refuses_narrowing() {
        let mut env = Environment::with_prelude();
        seed_sext_model(&mut env, MachineSIntWidth::I64, MachineSIntWidth::I128)
            .expect("the (i64 -> i128) sign-extension model must seed");
        let stored = env
            .get_const(&Name::from_string("trust_checked_sextI64toI128"))
            .and_then(|c| c.value.clone())
            .expect("the seeded model must have a value");
        let expected = Expr::lam(
            BinderInfo::Default,
            Domain::Signed(MachineSIntWidth::I64).ty(),
            Expr::app(
                Expr::const_(Name::from_string("trust_checked_ofInt128"), vec![]),
                Expr::app(
                    Expr::const_(Name::from_string("trust_checked_toInt64"), vec![]),
                    Expr::bvar(0),
                ),
            ),
        );
        assert_eq!(stored, expected, "sext is `ofInt(TARGET) (toInt(SOURCE) v)`, exactly");

        // Idempotent: seeding again is a no-op, not a homonym conflict.
        seed_sext_model(&mut env, MachineSIntWidth::I64, MachineSIntWidth::I128)
            .expect("re-seeding the same model must be accepted");

        // A NARROWING or same-width request is refused: the re-embed would be
        // a wrapping truncation and the name would be a lie.
        for (from, to) in [
            (MachineSIntWidth::I128, MachineSIntWidth::I64),
            (MachineSIntWidth::I64, MachineSIntWidth::I64),
        ] {
            assert!(
                seed_sext_model(&mut env, from, to).is_err(),
                "({from:?} -> {to:?}) is not a widening and must fail closed"
            );
        }
    }

    /// A select whose signature is NOT homogeneous. `sat_term(degree: i64,
    /// coeff: i64, lit: Lit)` flattens to a mixed carrier list, and the old
    /// all-equal rule refused it outright -- which is what made a per-term rule
    /// step impossible to mint. The `ite` encoding constrains only the compared
    /// pair and the branch pair; every other binder is just a binder.
    #[test]
    fn admit_select_function_mints_over_a_mixed_signature() {
        let mut env = Environment::with_prelude();
        let i = Domain::Signed(MachineSIntWidth::I64);
        let b = Domain::Bool;
        // fn cap(degree: i64, coeff: i64, flag: bool) -> i64
        //     { if coeff <= degree { coeff } else { degree } }
        admit_select_function(
            &mut env,
            "cap_mixed_def",
            &[i.clone(), i.clone(), b],
            SelectCmp::Le,
            1,
            0,
            1,
            0,
        )
        .expect("a select over a mixed signature must admit");

        // …and it still DECIDES correctly: the extra binder changes nothing.
        let tc = clean_kernel::TypeChecker::new(&env);
        let n = |v: i128| i.numeral(v as u128).unwrap();
        let tt = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let app = |d: i128, c: i128| {
            Expr::apps(
                Expr::const_(Name::from_string("cap_mixed_def"), vec![]),
                [n(d), n(c), tt.clone()],
            )
        };
        assert!(tc.is_def_eq(&app(3, 5), &n(3)), "cap(3, 5) = 3 -- coeff exceeds the degree");
        assert!(tc.is_def_eq(&app(5, 3), &n(3)), "cap(5, 3) = 3 -- coeff is under the degree");
    }

    /// A BitVec literal is a typed constructor, not the native reducer's old
    /// untyped Nat payload. Exercise the signed select with genuine carrier
    /// terms, and ask the kernel to check proofs of the result rather than
    /// granting the refused constructor fold authority in the fixture.
    #[test]
    fn typed_signed_bitvec_values_preserve_kernel_and_counterexample_controls() {
        for width in [MachineSIntWidth::I64, MachineSIntWidth::I128] {
            let d = Domain::Signed(width);
            let mut env = Environment::with_prelude();
            assert!(matches!(
                env.native_fold_verdict(&Name::from_string("BitVec.ofNat")),
                Err(clean_kernel::env::FoldRefusal::ReviewRefused { .. })
            ));
            for (name, then_param, else_param) in [("typed_min", 0, 1), ("typed_max", 1, 0)] {
                admit_select_function(
                    &mut env,
                    name,
                    &[d.clone(), d.clone()],
                    SelectCmp::Lt,
                    0,
                    1,
                    then_param,
                    else_param,
                )
                .expect("typed signed select must admit");
            }
            let tc = clean_kernel::TypeChecker::new(&env);
            let ty = d.ty();
            let three = d.numeral(3).unwrap();
            tc.check_type(&three, &ty).expect("literal has the genuine BitVec carrier");
            assert!(tc.check_type(&kernel_nat_lit(3), &ty).is_err(), "raw Nat is not BitVec");
            assert!(!tc.is_def_eq(&three, &kernel_nat_lit(3)), "refused payload collapse stays refused");
            assert!(tc.is_def_eq(&d.bitvec_to_nat(three).unwrap(), &kernel_nat_lit(3)));

            let one = d.numeral(1).unwrap();
            let minus_one = d.negative_numeral(1).unwrap();
            let app = |name: &str, a: Expr, b: Expr| {
                Expr::apps(Expr::const_(Name::from_string(name), vec![]), [a, b])
            };
            let equation = |lhs: Expr, rhs: Expr| {
                Expr::apps(
                    Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                    [ty.clone(), lhs, rhs],
                )
            };
            let refl = |value: Expr| {
                Expr::apps(
                    Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]),
                    [ty.clone(), value],
                )
            };
            let min = app("typed_min", minus_one.clone(), one.clone());
            let max = app("typed_max", minus_one.clone(), one.clone());
            for (actual, expected) in [(min.clone(), minus_one.clone()), (max.clone(), one.clone())] {
                tc.check_type(&actual, &ty).expect("actual select result is well-typed");
                let goal = equation(actual, expected.clone());
                tc.check_type(&goal, &Expr::prop()).expect("the exact result goal is a proposition");
                tc.check_type(&refl(expected), &goal).expect("kernel checks the signed result");
            }
            for (actual, wrong) in [(min.clone(), one), (max, minus_one)] {
                let goal = equation(actual, wrong.clone());
                tc.check_type(&goal, &Expr::prop()).expect("counterexample goal is well-typed");
                assert!(tc.check_type(&refl(wrong), &goal).is_err(), "wrong signed result is rejected");
            }
            if width == MachineSIntWidth::I128 {
                let truncated = d.bitvec_of_nat(kernel_nat_lit(u128::from(u64::MAX))).unwrap();
                let goal = equation(min, truncated.clone());
                tc.check_type(&goal, &Expr::prop()).expect("truncated-pattern goal is well-typed");
                assert!(tc.check_type(&refl(truncated), &goal).is_err(), "64-bit truncation is not -1 at 128 bits");
                let narrow = Domain::Signed(MachineSIntWidth::I64).negative_numeral(1).unwrap();
                let wrong_width = app("typed_min", narrow, d.numeral(1).unwrap());
                assert!(tc.check_type(&wrong_width, &ty).is_err(), "mixed-width arguments are rejected");
            }
        }
    }

    /// E6 widening increment 4: the SIGNED select mint. The semantic teeth are
    /// the mixed-sign rows — under the UNSIGNED reading `-1` is `2^64 - 1`, so
    /// `min2(-1, 1)` would reduce to `1`; the sign-flip keys must give `-1`.
    /// A mint that quietly compared raw `toNat` order would typecheck and
    /// pass every same-sign row, and ONLY these rows catch it.
    #[test]
    fn admit_select_function_mints_signed_min_and_max() {
        let mut env = Environment::with_prelude();
        let i = Domain::Signed(MachineSIntWidth::I64);
        // fn min2(a, b) -> i64 { if a < b { a } else { b } }
        admit_select_function(
            &mut env,
            "smin2_def",
            &[i.clone(), i.clone()],
            SelectCmp::Lt,
            0,
            1,
            0,
            1,
        )
        .expect("signed min2 must admit");
        // fn max2(a, b) -> i64 { if a < b { b } else { a } }
        admit_select_function(
            &mut env,
            "smax2_def",
            &[i.clone(), i.clone()],
            SelectCmp::Lt,
            0,
            1,
            1,
            0,
        )
        .expect("signed max2 must admit");
        // fn sel_eq(a, b) -> i64 { if a == b { a } else { b } } — the Eq arm.
        admit_select_function(
            &mut env,
            "seq_def",
            &[i.clone(), i.clone()],
            SelectCmp::Eq,
            0,
            1,
            0,
            1,
        )
        .expect("signed eq-select must admit");

        // Non-BitVec / non-machine domains still fail closed (checked before
        // the immutable TypeChecker borrow below).
        assert!(
            admit_select_function(
                &mut env,
                "bool_sel",
                &[Domain::Bool, Domain::Bool],
                SelectCmp::Eq,
                0,
                1,
                0,
                1,
            )
            .is_err(),
            "bool select stays outside the fragment"
        );

        let tc = clean_kernel::TypeChecker::new(&env);
        // Genuine BitVec inputs: the pinned kernel refuses the old native
        // ofNat-to-raw-Nat collapse because it changes the carrier. Observe
        // the exact numeric payload through the reviewed toNat projection;
        // keep every select result at BitVec64, not at an ill-typed Nat.
        let bits = |pattern: u128| i.bitvec_of_nat(kernel_nat_lit(pattern)).unwrap();
        let p = |v: u64| i.numeral(u128::from(v)).unwrap();
        // Negative value -v as its two's-complement 64-bit pattern.
        let m = |v: u64| i.negative_numeral(u128::from(v)).unwrap();
        tc.check_type(&p(3), &i.ty()).expect("the positive numeral has its carrier type");
        tc.check_type(&m(1), &i.ty()).expect("the negative numeral has its carrier type");
        tc.check_type(&kernel_nat_lit(3), &i.ty())
            .expect_err("a raw Nat is not a typed BitVec argument");
        assert!(
            tc.is_def_eq(&i.bitvec_to_nat(i.numeral(3).unwrap()).unwrap(), &kernel_nat_lit(3)),
            "the typed BitVec64 literal has the exact Nat payload 3"
        );
        assert!(
            tc.is_def_eq(&i.negative_numeral(1).unwrap(), &bits(u128::from(u64::MAX))),
            "the negative_numeral embedding has the exact typed bit pattern"
        );
        assert!(
            tc.is_def_eq(&i.bitvec_to_nat(m(1)).unwrap(), &kernel_nat_lit(u128::from(u64::MAX))),
            "BitVec.toNat of the production negative numeral is its exact 64-bit pattern"
        );
        let app2 = |f: &str, a: Expr, b: Expr| {
            let application = Expr::apps(Expr::const_(Name::from_string(f), vec![]), [a, b]);
            tc.check_type(&application, &i.ty())
                .unwrap_or_else(|e| panic!("{f} must be a well-typed carrier application: {e:?}"));
            application
        };
        // Same-sign rows (any order encoding passes these).
        assert!(tc.is_def_eq(&app2("smin2_def", p(3), p(5)), &p(3)), "min2(3,5) = 3");
        assert!(tc.is_def_eq(&app2("smax2_def", p(3), p(5)), &p(5)), "max2(3,5) = 5");
        // MIXED-SIGN rows — the rows an unsigned-order mint gets WRONG.
        assert!(tc.is_def_eq(&app2("smin2_def", m(1), p(1)), &m(1)), "min2(-1,1) = -1");
        assert!(tc.is_def_eq(&app2("smin2_def", p(1), m(1)), &m(1)), "min2(1,-1) = -1");
        assert!(tc.is_def_eq(&app2("smax2_def", m(1), p(1)), &p(1)), "max2(-1,1) = 1");
        // Both negative: -3 < -1 in signed order (unsigned order agrees here,
        // but the row pins the negative-negative quadrant regardless).
        assert!(tc.is_def_eq(&app2("smin2_def", m(3), m(1)), &m(3)), "min2(-3,-1) = -3");
        // i64::MIN vs 0 — the exact divergence the natural BitVec spelling
        // would have minted: unsigned order calls MIN the LARGER value.
        let min64 = i.negative_numeral(1u128 << 63).unwrap();
        assert!(tc.is_def_eq(&min64, &bits(1u128 << 63)), "the typed i64 minimum has its exact bit pattern");
        assert!(
            tc.is_def_eq(&app2("smin2_def", min64.clone(), p(0)), &min64),
            "min2(i64::MIN, 0) = i64::MIN"
        );
        // The Eq arm decides bit equality: eq-select(3, 3) takes THEN,
        // eq-select(3, 5) takes ELSE. Small magnitudes on purpose: today's
        // kernel reduces `Nat.decEq` by its unary `Nat.rec` tower when the
        // operands are not yet syntactic literals (no accelerated decision
        // tower like `Nat.decLt`/`Nat.decLe`), so a 2^64-magnitude operand
        // PARKS — declines, never wrong — and cannot be asserted here. Branch
        // wiring is fully distinguished at any magnitude; sign plays no role
        // in bit equality.
        assert!(tc.is_def_eq(&app2("seq_def", p(3), p(3)), &p(3)), "eq(3,3) takes then");
        assert!(tc.is_def_eq(&app2("seq_def", p(3), p(5)), &p(5)), "eq(3,5) takes else");
    }

    /// E6 widening increment 5: the comparison-to-bool mint
    /// (`fn le(a, b) -> bool { a <= b }`), over both an unsigned and a signed
    /// carrier. Semantic validation by definitional reduction of the returned
    /// BOOL — and again the mixed-sign row is the one an unsigned-order mint
    /// gets wrong (`-1 <= 1` is true in signed order, false in raw bit order).
    #[test]
    fn admit_comparison_function_mints_signed_and_unsigned_bool_decisions() {
        let mut env = Environment::with_prelude();
        let u = Domain::Machine(MachineUIntWidth::U64);
        let i = Domain::Signed(MachineSIntWidth::I64);
        admit_comparison_function(
            &mut env,
            "ule_def",
            &[u.clone(), u.clone()],
            SelectCmp::Le,
            CmpOperand::Param(0),
            CmpOperand::Param(1),
        )
        .expect("u64 le must admit");
        admit_comparison_function(
            &mut env,
            "sle_def",
            &[i.clone(), i.clone()],
            SelectCmp::Le,
            CmpOperand::Param(0),
            CmpOperand::Param(1),
        )
        .expect("i64 le must admit");
        admit_comparison_function(
            &mut env,
            "seq_def",
            &[i.clone(), i.clone()],
            SelectCmp::Eq,
            CmpOperand::Param(0),
            CmpOperand::Param(1),
        )
        .expect("i64 eq must admit");
        // Bool / Nat domains fail closed.
        assert!(
            admit_comparison_function(
                &mut env,
                "bool_cmp",
                &[Domain::Bool, Domain::Bool],
                SelectCmp::Eq,
                CmpOperand::Param(0),
                CmpOperand::Param(1)
            )
            .is_err(),
            "bool comparison stays outside the fragment"
        );
        // Mixed domains fail closed.
        assert!(
            admit_comparison_function(
                &mut env,
                "mixed_cmp",
                &[u.clone(), i.clone()],
                SelectCmp::Le,
                CmpOperand::Param(0),
                CmpOperand::Param(1)
            )
            .is_err(),
            "mixed-domain comparison stays outside the fragment"
        );

        let tc = clean_kernel::TypeChecker::new(&env);
        let btrue = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let bfalse = Expr::const_(Name::from_string("Bool.false"), vec![]);
        let app2 = |f: &str, a: Expr, b: Expr| {
            let application = Expr::apps(Expr::const_(Name::from_string(f), vec![]), [a, b]);
            tc.check_type(&application, &Expr::const_str("Bool"))
                .unwrap_or_else(|e| panic!("{f} must be a well-typed Bool application: {e:?}"));
            application
        };
        // u64 rows: UInt64 values are the carrier's own numerals.
        let un = |v: u64| u.numeral(u128::from(v)).unwrap();
        assert!(tc.is_def_eq(&app2("ule_def", un(3), un(5)), &btrue), "u64: 3 <= 5");
        assert!(tc.is_def_eq(&app2("ule_def", un(5), un(3)), &bfalse), "u64: !(5 <= 3)");
        // Signed rows use actual typed BitVec arguments, and the helper
        // checks every application before examining its Bool result.
        let p = |v: u64| i.numeral(u128::from(v)).unwrap();
        let m = |v: u64| i.negative_numeral(u128::from(v)).unwrap();
        assert!(tc.is_def_eq(&app2("sle_def", p(3), p(5)), &btrue), "i64: 3 <= 5");
        assert!(tc.is_def_eq(&app2("sle_def", p(5), p(3)), &bfalse), "i64: !(5 <= 3)");
        // MIXED-SIGN rows.
        assert!(tc.is_def_eq(&app2("sle_def", m(1), p(1)), &btrue), "i64: -1 <= 1");
        assert!(tc.is_def_eq(&app2("sle_def", p(1), m(1)), &bfalse), "i64: !(1 <= -1)");
        let min64 = i.negative_numeral(1u128 << 63).unwrap();
        assert!(tc.is_def_eq(&app2("sle_def", min64, p(0)), &btrue), "i64: MIN <= 0");
        // Eq rows (small magnitudes; see the decEq tower note above).
        assert!(tc.is_def_eq(&app2("seq_def", p(3), p(3)), &btrue), "i64: 3 == 3");
        assert!(tc.is_def_eq(&app2("seq_def", p(3), p(5)), &bfalse), "i64: !(3 == 5)");
    }

    /// E6 widening increment 6: a LITERAL operand in the comparison mint — the
    /// shape every width guard is written in (`x <= HI`, `LO <= x`, `x >= 0`).
    ///
    /// The property that matters is not "the mint typechecks" but "the mint is
    /// the term the CLAUSE builds for the same source", so the pin is a
    /// definitional-equality check between the minted body and the elaboration
    /// of `f(x) == (x >= 0)`. That is what makes the postcondition close by
    /// `Eq.refl`, and it is sensitive to exactly what a typing check is blind
    /// to: which of `Domain::zero` / `numeral` / `negative_numeral` the literal
    /// takes, and which side of the relation the `>=` swap put it on.
    ///
    /// Unsigned rows additionally reduce, so they are also checked by VALUE.
    /// Signed rows cannot be: at a `BitVec` carrier
    /// `BitVec.toNat (BitVec.ofNat w n)` PARKS (the collapse
    /// `BitVec.ofNat w n ≡ n` is an `is_def_eq` rule, not an iota step a
    /// projection fires through), so a minted signed literal's order key is a
    /// stuck term. That costs the discharge nothing — both sides build the same
    /// stuck term — but it is why the signed evidence here is the defeq pin
    /// rather than a reduction table.
    #[test]
    fn admit_comparison_function_mints_literal_bounds_and_refuses_out_of_range() {
        let i8d = Domain::Signed(MachineSIntWidth::I8);
        let u8d = Domain::Machine(MachineUIntWidth::U8);

        // FAIL CLOSED: a literal outside the carrier is refused, never wrapped
        // through `ofNat` (`UInt8.ofNat 300 = 44` is exactly the silent wrong
        // answer this check exists to prevent).
        let mut env = Environment::with_prelude();
        for (name, d, op) in [
            ("over_u8", u8d.clone(), CmpOperand::Const(256)),
            ("over_i8", i8d.clone(), CmpOperand::Const(128)),
            ("under_i8", i8d.clone(), CmpOperand::NegConst(129)),
        ] {
            assert!(
                admit_comparison_function(
                    &mut env,
                    name,
                    &[d],
                    SelectCmp::Le,
                    CmpOperand::Param(0),
                    op,
                )
                .is_err(),
                "{name}: an out-of-carrier literal must fail closed"
            );
        }
        // ...but the exact boundaries are IN range.
        admit_comparison_function(
            &mut env,
            "at_i8_min",
            &[i8d.clone()],
            SelectCmp::Le,
            CmpOperand::NegConst(128),
            CmpOperand::Param(0),
        )
        .expect("the exact i8 minimum is representable");
        admit_comparison_function(
            &mut env,
            "at_u8_max",
            &[u8d.clone()],
            SelectCmp::Le,
            CmpOperand::Param(0),
            CmpOperand::Const(255),
        )
        .expect("the exact u8 maximum is representable");
        // FAIL CLOSED: two literals leave no parameter fixing the carrier.
        assert!(
            admit_comparison_function(
                &mut env,
                "both_const",
                &[u8d],
                SelectCmp::Le,
                CmpOperand::Const(1),
                CmpOperand::Const(2),
            )
            .is_err(),
            "a two-literal comparison must fail closed"
        );

        // THE DEFEQ PIN, at a signed and an unsigned carrier and for a zero, a
        // negative and a positive bound. Each row mints the body rustc lowers
        // for `fn f(x) -> bool { x <cmp> <lit> }` and elaborates the clause
        // `f(x) == (x <cmp> <lit>)` against it.
        for (rust_ty, dom, clause, cmp, left, right) in [
            // `x >= 0` lowers to `Ge(x, 0)`, normalized to `Le(0, x)`.
            (
                "i64",
                Domain::Signed(MachineSIntWidth::I64),
                "f(x) == (x >= 0)",
                SelectCmp::Le,
                CmpOperand::Const(0),
                CmpOperand::Param(0),
            ),
            (
                "i64",
                Domain::Signed(MachineSIntWidth::I64),
                "f(x) == (x >= -1)",
                SelectCmp::Le,
                CmpOperand::NegConst(1),
                CmpOperand::Param(0),
            ),
            (
                "u64",
                Domain::Machine(MachineUIntWidth::U64),
                "f(x) == (x <= 255)",
                SelectCmp::Le,
                CmpOperand::Param(0),
                CmpOperand::Const(255),
            ),
        ] {
            let mut env = Environment::with_prelude();
            let adm =
                admit_comparison_function(&mut env, "f_def", &[dom.clone()], cmp, left, right)
                    .unwrap_or_else(|e| panic!("`{clause}` mint must admit: {e}"));
            let t = admitted_table("f", adm);
            let goal = elaborate_goal_typed_with_facets(clause, &[("x", rust_ty)], &t)
                .unwrap_or_else(|e| panic!("`{clause}` must elaborate: {e}"));
            let tc = clean_kernel::TypeChecker::new(&env);
            let _ = tc
                .infer_type(&goal)
                .unwrap_or_else(|e| panic!("`{clause}` must be well-typed: {e:?}"));
            let (carrier, lhs, rhs) = eq_core(&goal);
            assert_eq!(carrier, Expr::const_(Name::from_string("Bool"), vec![]));
            assert!(
                tc.is_def_eq(&lhs, &rhs),
                "`{clause}`: the literal-bound mint and the clause must agree"
            );
        }

        // UNSIGNED rows also reduce, so the decision is checked by VALUE —
        // on both sides of the boundary and on it.
        let mut env = Environment::with_prelude();
        let u = Domain::Machine(MachineUIntWidth::U8);
        admit_comparison_function(
            &mut env,
            "le200_def",
            &[u.clone()],
            SelectCmp::Le,
            CmpOperand::Param(0),
            CmpOperand::Const(200),
        )
        .expect("u8 literal bound must admit");
        let tc = clean_kernel::TypeChecker::new(&env);
        let btrue = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let bfalse = Expr::const_(Name::from_string("Bool.false"), vec![]);
        let app1 = |f: &str, a: Expr| Expr::app(Expr::const_(Name::from_string(f), vec![]), a);
        let un = |v: u8| u.numeral(u128::from(v)).unwrap();
        assert!(tc.is_def_eq(&app1("le200_def", un(199)), &btrue), "u8: 199 <= 200");
        assert!(tc.is_def_eq(&app1("le200_def", un(200)), &btrue), "u8: 200 <= 200");
        assert!(tc.is_def_eq(&app1("le200_def", un(201)), &bfalse), "u8: !(201 <= 200)");
    }

    /// E6 widening increment 6, width half: `i128` is in the import width
    /// table, and its order key is the sign flip at `2^127`.
    ///
    /// The exact key is pinned STRUCTURALLY, not by a Debug substring: a `u128`
    /// literal is a multi-limb kernel node, so a decimal-substring check would
    /// silently pass on nothing.
    #[test]
    fn i128_admits_and_pins_the_two_pow_127_order_key() {
        let d = Domain::Signed(MachineSIntWidth::I128);
        assert_eq!(d.bitvec_bits(), Some(128));
        let expected_key = Expr::apps(
            Expr::const_(Name::from_string("Nat.xor"), vec![]),
            [
                Expr::apps(
                    Expr::const_(Name::from_string("BitVec.toNat"), vec![]),
                    [Expr::nat_lit(128), Expr::bvar(0)],
                ),
                kernel_nat_lit(1u128 << 127),
            ],
        );
        assert_eq!(
            d.bitvec_order_key(Expr::bvar(0)).expect("i128 has an order key"),
            expected_key,
            "the i128 order key must flip the 2^127 sign bit"
        );

        // The `2^127` boundary is exactly representable and one past it is not.
        assert!(d.negative_numeral(1u128 << 127).is_ok(), "i128 MIN is in range");
        assert!(d.negative_numeral((1u128 << 127) + 1).is_err(), "below i128 MIN fails closed");
        assert!(d.numeral((1u128 << 127) - 1).is_ok(), "i128 MAX is in range");
        assert!(d.numeral(1u128 << 127).is_err(), "above i128 MAX fails closed");

        let mut env = Environment::with_prelude();
        admit_comparison_function(
            &mut env,
            "wle_def",
            &[d.clone(), d.clone()],
            SelectCmp::Le,
            CmpOperand::Param(0),
            CmpOperand::Param(1),
        )
        .expect("an i128 comparison must admit");
        admit_select_function(
            &mut env,
            "wmin_def",
            &[d.clone(), d.clone()],
            SelectCmp::Lt,
            0,
            1,
            0,
            1,
        )
        .expect("an i128 select must admit");

        let tc = clean_kernel::TypeChecker::new(&env);
        let btrue = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let bfalse = Expr::const_(Name::from_string("Bool.false"), vec![]);
        let app2 = |f: &str, a: Expr, b: Expr| {
            let application = Expr::apps(Expr::const_(Name::from_string(f), vec![]), [a, b]);
            let result_type = if f == "wle_def" { Expr::const_str("Bool") } else { d.ty() };
            tc.check_type(&application, &result_type)
                .unwrap_or_else(|e| panic!("{f} must be a well-typed application: {e:?}"));
            application
        };
        // A real BitVec128 constructor contains the exact two's-complement
        // pattern. A raw Nat is not its carrier; the refused native collapse
        // must not be required for a semantic test to reach its signed rows.
        let bits = |pattern: u128| d.bitvec_of_nat(kernel_nat_lit(pattern)).unwrap();
        let v = |x: i128| {
            if x >= 0 {
                d.numeral(x as u128).unwrap()
            } else {
                d.negative_numeral(x.unsigned_abs()).unwrap()
            }
        };
        tc.check_type(&v(3), &d.ty()).expect("the numeral has its BitVec 128 carrier type");
        tc.check_type(&kernel_nat_lit(3), &d.ty())
            .expect_err("a raw Nat is not a typed BitVec 128 argument");
        assert!(
            tc.is_def_eq(&d.bitvec_to_nat(d.numeral(3).unwrap()).unwrap(), &kernel_nat_lit(3)),
            "the typed BitVec128 literal has the exact Nat payload 3"
        );
        assert!(tc.is_def_eq(&app2("wle_def", v(3), v(5)), &btrue), "i128: 3 <= 5");
        assert!(tc.is_def_eq(&app2("wle_def", v(5), v(3)), &bfalse), "i128: !(5 <= 3)");
        assert!(tc.is_def_eq(&app2("wmin_def", v(3), v(5)), &v(3)), "i128: min2(3, 5) = 3");

        assert!(tc.is_def_eq(&d.negative_numeral(1u128 << 63).unwrap(), &bits(i128::from(i64::MIN) as u128)));
        assert!(tc.is_def_eq(&d.numeral(i64::MAX as u128).unwrap(), &bits(i64::MAX as u128)));
        assert!(tc.is_def_eq(&d.negative_numeral(1u128 << 127).unwrap(), &bits(1u128 << 127)));
        // Observe every multi-limb embedding through its typed toNat
        // projection, retaining all three original boundary patterns.
        for (value, pattern) in [
            (d.negative_numeral(1u128 << 63).unwrap(), i128::from(i64::MIN) as u128),
            (d.numeral(i64::MAX as u128).unwrap(), i64::MAX as u128),
            (d.negative_numeral(1u128 << 127).unwrap(), i128::MIN as u128),
        ] {
            tc.check_type(&value, &d.ty()).expect("a checked multi-limb carrier value");
            assert!(
                tc.is_def_eq(&d.bitvec_to_nat(value).unwrap(), &kernel_nat_lit(pattern)),
                "the typed boundary numeral must project to {pattern}"
            );
        }
        assert!(
            tc.is_def_eq(&d.bitvec_to_nat(v(-1)).unwrap(), &kernel_nat_lit(u128::MAX)),
            "BitVec.toNat of the typed all-ones value is the multi-limb payload"
        );
        // …and the MIXED-SIGN COMPARISON rows at i128, previously impossible
        // because the order key routes through `toNat`: negative < positive,
        // positive !< negative, and the extreme boundary pair — the i64 rows
        // validate the sign-flip ENCODING, these now validate it at the width
        // whose negative patterns are all multi-limb.
        assert!(tc.is_def_eq(&app2("wle_def", v(-1), v(0)), &btrue), "i128: -1 <= 0");
        assert!(tc.is_def_eq(&app2("wle_def", v(0), v(-1)), &bfalse), "i128: !(0 <= -1)");
        assert!(
            tc.is_def_eq(&app2("wle_def", v(i128::MIN), v(i128::MAX)), &btrue),
            "i128: MIN <= MAX"
        );
        assert!(
            tc.is_def_eq(&app2("wle_def", v(i128::MAX), v(i128::MIN)), &bfalse),
            "i128: !(MAX <= MIN)"
        );
        assert!(
            tc.is_def_eq(&app2("wmin_def", v(-1), v(1)), &v(-1)),
            "i128: min2(-1, 1) = -1 — the signed order, not the unsigned one"
        );
        // The DISCHARGE lane is indifferent either way: it compares the
        // clause's term with the mint's, and both build the same application,
        // which now reduces on both sides symmetrically.

        // And the clause elaborator agrees at the same width — `i128` is a
        // supported E3 binder and its comparison uses the very same key.
        let goal = elaborate_goal_typed("x <= y", &[("x", "i128"), ("y", "i128")])
            .expect("an i128 clause must elaborate");
        let clause_key = Expr::apps(
            Expr::const_(Name::from_string("Nat.xor"), vec![]),
            [
                Expr::apps(
                    Expr::const_(Name::from_string("BitVec.toNat"), vec![]),
                    [Expr::nat_lit(128), Expr::bvar(1)],
                ),
                kernel_nat_lit(1u128 << 127),
            ],
        );
        let expected_goal = Expr::pi(
            BinderInfo::Default,
            d.ty(),
            Expr::pi(
                BinderInfo::Default,
                d.ty(),
                nat_pred("Nat.le", clause_key, d.bitvec_order_key(Expr::bvar(0)).unwrap()),
            ),
        );
        assert_eq!(goal, expected_goal, "the i128 clause drifted from the mint's order key");
    }

    /// v7/D3 for the measured `spec::first` refusal (alab-rust probes p4/p5,
    /// 2026-09-16): an island definition admitted under its bare Clean name,
    /// cited through a Rust module path, STAYS refused — and now says that the
    /// spelling is the problem, with options.
    #[test]
    fn a_module_qualified_island_spelling_stays_refused_and_names_the_bare_clean_name() {
        use trust_symbols::KernelAuthority as _;
        let cert = || FacetStatus::Certified { evidence: "test".into() };
        let admissible =
            || FnFacets { pure: cert(), total: cert(), deterministic: cert(), no_panic: cert() };
        let vt: &[(&str, &str)] = &[("a", "u64"), ("b", "u64")];
        let kernel_checked = trust_symbols::CicKernelRecheck::held_by_kernel_recheck()
            .kernel_checked(
                trust_symbols::TermDigest::of_bytes(b"def first (a b : UInt64) : UInt64 := a"),
                trust_symbols::AxiomClosure::audited([]),
            );

        let mut t = FacetTable::new();
        t.insert("first", admissible());
        t.admit("first", Admission::kernel_checked("first", 2, kernel_checked));

        // POSITIVE: the refusal is kept verbatim, and the hint follows it.
        let err = elaborate_goal_typed_with_facets("spec::first(a, b) <= a", vt, &t).unwrap_err();
        assert!(err.contains("no diagnostic E6 facet record exists for `spec::first`"), "{err}");
        assert!(err.contains("under the bare Clean name `first`"), "{err}");
        assert!(err.contains("options: (1)") && err.contains("(2)"), "{err}");
        assert!(err.contains("write `first(..)`"), "{err}");

        // CLOSE NEGATIVE TWIN 1: the bare name under the qualified spelling is
        // a REFLECTED Rust carrier, not an island definition. No hint — telling
        // the author to write `cap(..)` would retarget the clause to a
        // different item's admission.
        let mut reflected = FacetTable::new();
        reflected.insert("cap", admissible());
        reflected.admit("cap", Admission::reflected("cap_const", 1));
        let vx: &[(&str, &str)] = &[("x", "u64")];
        let err =
            elaborate_goal_typed_with_facets("other::cap(x) <= x", vx, &reflected).unwrap_err();
        assert!(err.contains("no diagnostic E6 facet record exists for `other::cap`"), "{err}");
        assert!(!err.contains("bare Clean name"), "{err}");

        // CLOSE NEGATIVE TWIN 2: nothing at all under the bare name.
        let err = elaborate_goal_typed_with_facets("spec::absent(a, b) <= a", vt, &t).unwrap_err();
        assert!(!err.contains("bare Clean name"), "{err}");

        // CONTROL: the hint is wording only. The qualified spelling must not
        // have started elaborating through the bare admission.
        assert!(elaborate_goal_typed_with_facets("spec::first(a, b) <= a", vt, &t).is_err());
    }

    #[test]
    fn a_module_qualified_callee_spelling_elaborates_through_its_admission() {
        // The spelling the `veripb-core-proved` contract must use, because its
        // bare name `narrow` is owned by three items and stays evicted. A
        // multi-segment callee path must (a) key the admission lookup by the
        // JOINED path, and (b) contribute no free variable of its own — syn
        // reports `get_ident() == None` for it, so `collect_vars` skips it and
        // the exact-bijection gate still sees only `{x}`.
        let cert = || FacetStatus::Certified { evidence: "test".into() };
        let admissible =
            FnFacets { pure: cert(), total: cert(), deterministic: cert(), no_panic: cert() };
        let vt: &[(&str, &str)] = &[("x", "u64")];

        let mut t = FacetTable::new();
        t.insert("guard::cap", admissible);
        t.admit(
            "guard::cap",
            Admission::reflected("guard_cap_const", 1),
        );

        let goal = elaborate_goal_typed_with_facets("guard::cap(x) <= x", vt, &t)
            .expect("admitted qualified call must elaborate");
        assert!(
            format!("{goal:?}").contains("guard_cap_const"),
            "goal must apply the kernel constant: {goal:?}"
        );

        // The BARE spelling of the same item is a different key and confers
        // nothing — which is exactly why an ambiguity-evicted bare name stays
        // fail-closed while the qualified spelling works.
        let err = elaborate_goal_typed_with_facets("cap(x) <= x", vt, &t).unwrap_err();
        assert!(err.contains("no diagnostic E6 facet record exists for `cap`"), "{err}");

        // And a qualified spelling with no record fails closed under its full
        // joined path, not under its last segment.
        let err = elaborate_goal_typed_with_facets("other::cap(x) <= x", vt, &t).unwrap_err();
        assert!(err.contains("no diagnostic E6 facet record exists for `other::cap`"), "{err}");
    }

    #[test]
    fn spec_spellings_enumerates_proper_suffixes_of_a_plain_module_path() {
        // The `veripb-core-proved` shape this exists for: the free function
        // is uniquely determined by `guard::narrow`, which was previously not
        // a key at all.
        assert_eq!(spec_spellings("lib::guard::narrow"), vec!["narrow", "guard::narrow"]);
        assert_eq!(spec_spellings("krate::a::b::c::f"), vec!["f", "c::f", "b::c::f", "a::b::c::f"]);
        // The full def-path is NEVER re-emitted — the caller keys it itself,
        // and re-emitting it would make a root-level function collide with
        // its own def-path key.
        assert!(!spec_spellings("lib::guard::narrow").iter().any(|s| s == "lib::guard::narrow"));
        assert_eq!(spec_spellings("lib::narrow"), vec!["narrow"]);
    }

    #[test]
    fn spec_spellings_of_a_non_identifier_def_path_is_the_bare_name_only() {
        // A trait-impl method: `CoeffDomain>::narrow` is not a spelling any
        // Rust source can write, so only the last segment is offered — which
        // is exactly what must still collide with `lib::guard::narrow`'s bare
        // name and evict it.
        assert_eq!(spec_spellings("<i64 as lib::CoeffDomain>::narrow"), vec!["narrow"]);
        assert_eq!(
            spec_spellings("<malachite_bigint::bigint::BigInt as lib::CoeffDomain>::narrow"),
            vec!["narrow"]
        );
        assert_eq!(spec_spellings("lib::Constraint::<C>::coeff_sum"), vec!["coeff_sum"]);
    }

    #[test]
    fn spec_spellings_of_a_root_or_unspellable_path_is_empty() {
        // Single segment: already keyed under itself, no proper suffix.
        assert!(spec_spellings("narrow").is_empty());
        assert!(spec_spellings("").is_empty());
        // A last segment that is not a plain identifier is not spellable at
        // all, so nothing is keyed for it (fail closed).
        assert!(spec_spellings("lib::f::<__trust_args@deadbeef>").is_empty());
        assert!(spec_spellings("lib::{closure#0}").is_empty());
        assert!(spec_spellings("lib::0").is_empty());
    }

    #[test]
    fn self_fn_spelling_is_the_def_path_for_a_plain_identifier_path() {
        // The ensures-discharge identity is the CANONICAL def-path whenever the
        // path is spellable as a call, so a contracted function whose bare name
        // is shared with other items still reaches its own record.
        assert_eq!(
            self_fn_spelling("veripb_core_proved::cap_coeff"),
            "veripb_core_proved::cap_coeff"
        );
        assert_eq!(self_fn_spelling("lib::guard::narrow"), "lib::guard::narrow");
        // A single-segment path is already its own def-path.
        assert_eq!(self_fn_spelling("cap_coeff"), "cap_coeff");
    }

    #[test]
    fn self_fn_spelling_falls_back_to_the_last_segment_for_an_unspellable_path() {
        // A qualified-impl head, a generic-argument list, or a synthetic segment
        // cannot be written as a spec CALL, and `callee_path` reconstructs a
        // DIFFERENT key from the parsed syntax (it drops the qself). Such a path
        // keeps the historical last-segment identity, which is subject to the
        // same ambiguity eviction as before — i.e. unchanged behaviour, never a
        // re-keying to another item.
        assert_eq!(self_fn_spelling("<i64 as lib::CoeffDomain>::cap_coeff"), "cap_coeff");
        assert_eq!(self_fn_spelling("lib::f::<__trust_args@deadbeef>"), "<__trust_args@deadbeef>");
        assert_eq!(self_fn_spelling("lib::{closure#0}"), "{closure#0}");
        assert_eq!(self_fn_spelling(""), "");
    }

    #[test]
    fn ensures_discharge_binds_result_through_the_def_path_when_the_bare_name_is_evicted() {
        // THE DEFECT (fixed 2026-08-26). `record_fn_facets` keys an item's
        // record under its canonical def-path AND every spellable suffix, and
        // evicts any key claimed by two def-paths — correct, fail-closed, and
        // KEPT. But the ensures lane derived the contracted function's OWN
        // identity from `tcx.item_name`, i.e. the BARE name, which re-entered
        // that keyspace: `veripb_core_proved::cap_coeff` shares `cap_coeff` with
        // the `CoeffDomain` method and its impls, so the bare key is evicted and
        // `result` could never be bound — the clause was then checked against
        // the forall-over-`result` reading, which is false.
        //
        // Reproduce the evicted table exactly, then show the def-path key
        // discharges what the bare key cannot.
        let mut env = Environment::with_prelude();
        let u64d = || Domain::Machine(MachineUIntWidth::U64);
        admit_projection_function(&mut env, "cap_coeff_def", &[u64d()], 0)
            .expect("identity admits");

        let cert = || FacetStatus::Certified { evidence: "test".into() };
        let admissible =
            FnFacets { pure: cert(), total: cert(), deterministic: cert(), no_panic: cert() };
        let adm = Admission::reflected("cap_coeff_def", 1);
        let mut facets = FacetTable::new();
        // The surviving canonical key…
        facets.insert("veripb_core_proved::cap_coeff", admissible.clone());
        facets.admit("veripb_core_proved::cap_coeff", adm.clone());
        // …and the bare spelling as `record_fn_facets` leaves it after a second
        // def-path (the trait method) claims it: evicted, no record.
        facets.insert("cap_coeff", admissible);
        facets.admit("cap_coeff", adm);
        facets.remove("cap_coeff");

        let params: &[(&str, &str)] = &[("x", "u64")];
        let tc = clean_kernel::TypeChecker::new(&env);

        // BEFORE the fix (bare identity): no record, no goal, fail closed.
        let bare_err = elaborate_ensures("result >= x", params, "cap_coeff", &facets)
            .expect_err("an evicted bare name must not bind `result`");
        assert!(bare_err.contains("E6-admitted"), "{bare_err}");

        // AFTER the fix (canonical def-path identity): the goal is built and
        // `result` is bound to the imported definition.
        let goal =
            elaborate_ensures("result >= x", params, "veripb_core_proved::cap_coeff", &facets)
                .expect("the canonical def-path must reach the surviving record");
        let want = elaborate_goal_typed("x >= x", params).unwrap();
        assert!(
            tc.is_def_eq(&goal, &want),
            "result must be bound to cap_coeff_def(x)=x:\n{goal:?}"
        );
        // …and it is NOT the forall-over-`result` reading the defect fell
        // through to.
        let result_universal =
            elaborate_goal_typed("result >= x", &[("result", "u64"), ("x", "u64")]).unwrap();
        assert!(
            !tc.is_def_eq(&goal, &result_universal),
            "the def-path lane must bind `result`, not forall-close over it"
        );
    }

    #[test]
    fn ensures_discharge_refuses_a_self_identity_that_does_not_round_trip() {
        // SOUNDNESS. The substitute spliced in for `result` is a PARSED call,
        // and the elaborator re-derives its admission key with `callee_path`,
        // which drops a qualified-impl qself. If the caller ever passed a key
        // the parser cannot reproduce, `result` could be bound to a DIFFERENT
        // item's defining equation than the one whose admission was checked.
        // Refuse instead. (`self_fn_spelling` never produces such a key; this is
        // the independent backstop.)
        let mut env = Environment::with_prelude();
        let u64d = || Domain::Machine(MachineUIntWidth::U64);
        admit_projection_function(&mut env, "narrow_def", &[u64d()], 0).expect("identity admits");

        let cert = || FacetStatus::Certified { evidence: "test".into() };
        let admissible =
            FnFacets { pure: cert(), total: cert(), deterministic: cert(), no_panic: cert() };
        let mut facets = FacetTable::new();
        // The qualified-impl head IS a legitimate facet-table key (that is how
        // `record_fn_facets` keys the item) — it is just not spellable.
        facets.insert("<i64 as lib::CoeffDomain>::narrow", admissible);
        facets.admit(
            "<i64 as lib::CoeffDomain>::narrow",
            Admission::reflected("narrow_def", 1),
        );

        let params: &[(&str, &str)] = &[("x", "u64")];
        let err =
            elaborate_ensures("result >= x", params, "<i64 as lib::CoeffDomain>::narrow", &facets)
                .expect_err("an unspellable self identity must fail closed");
        assert!(err.contains("not spellable as a spec call"), "{err}");
    }

    /// A `FacetTable` with `name` admitted at `adm` and all four facets
    /// certified — the shape the E6 import step installs.
    fn admitted_table(name: &str, adm: Admission) -> FacetTable {
        let cert = || FacetStatus::Certified { evidence: "test".into() };
        let mut t = FacetTable::new();
        t.insert(
            name,
            FnFacets { pure: cert(), total: cert(), deterministic: cert(), no_panic: cert() },
        );
        t.admit(name, adm);
        t
    }

    /// Strip a goal's Pi telescope and destructure the `Eq ty lhs rhs` at its
    /// core into `(ty, lhs, rhs)`.
    fn eq_core(goal: &Expr) -> (Expr, Expr, Expr) {
        let mut body = goal.clone();
        while let clean_kernel::ExprKind::Pi(_, _, codomain) = body.kind() {
            body = (**codomain).clone();
        }
        let clean_kernel::ExprKind::App(eq_ty_lhs, rhs) = body.kind() else {
            panic!("goal core must be an Eq application: {body:?}");
        };
        let clean_kernel::ExprKind::App(eq_ty, lhs) = eq_ty_lhs.kind() else {
            panic!("goal core must be a two-argument Eq: {body:?}");
        };
        let clean_kernel::ExprKind::App(_, ty) = eq_ty.kind() else {
            panic!("goal core must be a homogeneous Eq: {body:?}");
        };
        ((**ty).clone(), (**lhs).clone(), (**rhs).clone())
    }

    /// E6/E9 widening increment 8: the elaborator-level pin for typing a
    /// call's arguments by the CALLEE'S DECLARED carriers, and for every
    /// fail-closed condition that comes with it.
    ///
    /// The positive half is a `BitVec 64 -> BitVec 128 -> Bool` callee applied
    /// to an `i64` and an `i128` clause variable: two widths in one ARGUMENT
    /// LIST, which is not two widths in one comparison. The negative halves are
    /// the four ways the record can fail to justify a call, each of which must
    /// refuse rather than pick a carrier.
    #[test]
    fn a_call_types_its_arguments_by_the_callees_declared_carriers() {
        let i64d = Domain::Signed(MachineSIntWidth::I64);
        let i128d = Domain::Signed(MachineSIntWidth::I128);
        let vt: &[(&str, &str)] = &[("m", "i64"), ("t", "i128")];

        let mut env = Environment::with_prelude();
        let adm = admit_widened_eq_function(
            &mut env,
            "eq_ok_def",
            &[i64d.clone(), i128d.clone()],
            MachineSIntWidth::I64,
            MachineSIntWidth::I128,
            0,
            1,
            true,
        )
        .expect("the widened-equality mint must admit");
        assert_eq!(
            adm.carriers,
            Some(DeclaredCarriers {
                params: vec![Carrier::BitVec(64), Carrier::BitVec(128)],
                ret: Carrier::Bool,
            }),
            "the mint must record the mixed telescope it just handed the kernel"
        );
        let t = admitted_table("eq_ok", adm.clone());

        // POSITIVE: the mixed-width call elaborates, and the goal TYPECHECKS —
        // which is what the pre-increment "mixed domains in one comparison"
        // refusal was standing in front of.
        let goal = elaborate_goal_typed_with_facets("eq_ok(m, t)", vt, &t)
            .expect("a call at two declared widths must elaborate");
        let tc = clean_kernel::TypeChecker::new(&env);
        let ty = tc.infer_type(&goal).expect("the mixed-width goal must be well-typed");
        assert!(tc.is_def_eq(&ty, &Expr::sort(Level::zero())), "the goal must be a Prop");
        drop(tc);

        // NEG 1 — THE REFUSAL THAT MUST NOT MOVE. Two operands of different
        // widths in ONE comparison, with no typed callee between them: the
        // elaborator has no cast to justify it, so it is still an error.
        let err = elaborate_goal_typed_with_facets("m == t", vt, &t)
            .expect_err("a bare cross-width comparison must fail closed");
        assert!(err.contains("mixed domains in one comparison"), "{err}");
        let err = elaborate_goal_typed_with_facets("eq_ok(m, t) == (m == t)", vt, &t)
            .expect_err("a bare cross-width comparison must fail closed beside a typed call too");
        assert!(err.contains("mixed domains in one comparison"), "{err}");

        // NEG 2 — an argument whose OWN domain contradicts the declared
        // parameter carrier is named, never coerced.
        let err = elaborate_goal_typed_with_facets("eq_ok(t, t)", &[("t", "i128")], &t)
            .expect_err("an `i128` argument at a `BitVec 64` parameter must fail closed");
        assert!(err.contains("declares parameter 0 at carrier `BitVec 64`"), "{err}");

        // NEG 3 — an ARITY mismatch is refused before any carrier is consulted.
        let err = elaborate_goal_typed_with_facets("eq_ok(m)", &[("m", "i64")], &t)
            .expect_err("an arity mismatch must fail closed");
        assert!(err.contains("has arity 2 but is applied to 1"), "{err}");

        // NEG 4 — a callee with NO recorded declaration falls back to the one
        // ambient domain, so the mixed-width call it could not justify stays
        // refused exactly as it was before this increment. A missing record
        // buys nothing.
        let unrecorded = Admission { carriers: None, ..adm.clone() };
        let t_unrecorded = admitted_table("eq_ok", unrecorded);
        let err = elaborate_goal_typed_with_facets("eq_ok(m, t)", vt, &t_unrecorded)
            .expect_err("no recorded declaration must not admit a mixed-width call");
        assert!(err.contains("mixed domains in one comparison"), "{err}");

        // NEG 5 — a record whose LENGTH contradicts the recorded arity is two
        // disagreeing reads of one declaration; it is never indexed into, and
        // the call falls back to the same pre-increment refusal.
        let ragged = Admission {
            carriers: Some(DeclaredCarriers {
                params: vec![Carrier::BitVec(64)],
                ret: Carrier::Bool,
            }),
            ..adm
        };
        let t_ragged = admitted_table("eq_ok", ragged);
        let err = elaborate_goal_typed_with_facets("eq_ok(m, t)", vt, &t_ragged)
            .expect_err("a ragged carrier record must not admit a mixed-width call");
        assert!(err.contains("mixed domains in one comparison"), "{err}");
    }

    /// Mint each `(name, params, ret, body)` through the E6 tree mint the
    /// compiler uses for an `if`/`&&` body, under kernel constant `<name>_def`,
    /// and admit it with all four facets certified.
    fn tree_minted_table(
        env: &mut Environment,
        fns: &[(&str, &[Domain], &Domain, &E6TreeTerm)],
    ) -> FacetTable {
        let cert = || FacetStatus::Certified { evidence: "test".into() };
        let mut t = FacetTable::new();
        for (name, params, ret, body) in fns {
            let adm = admit_e6_tree_function(env, &format!("{name}_def"), params, ret, body)
                .unwrap_or_else(|e| panic!("the E6 tree mint must admit `{name}`: {e}"));
            assert_eq!(
                adm.carriers,
                Some(DeclaredCarriers::of_domains(params, ret)),
                "the tree mint must record the telescope it handed the kernel"
            );
            t.insert(
                *name,
                FnFacets { pure: cert(), total: cert(), deterministic: cert(), no_panic: cert() },
            );
            t.admit(*name, adm);
        }
        t
    }

    /// The RELATION carrier of `result == spec(..)` is the carrier the two
    /// typed calls RETURN, never the one their arguments share.
    ///
    /// The shape is aterm's `fn cursor(has: bool, fresh: bool, same: bool,
    /// continues: bool) -> u8` with `ensures result == spec_cursor(..) by
    /// cursor_is_exact` (Trust build 16387): every variable of the clause is a
    /// `bool`, so the first rule of `atom_domain` built `Eq Bool` over two
    /// `UInt8` terms, the kernel refused the goal as ill-typed and the citation
    /// was graded outside the fragment. Each positive row below is a goal that
    /// must TYPECHECK at the result's carrier and close by definitional equality
    /// against a mint of the same body, and must NOT close against a mint of a
    /// different one: a well-typed goal that anything proves would pin nothing.
    #[test]
    fn a_relation_between_typed_calls_takes_their_result_carrier_not_their_arguments() {
        use E6TreeTerm as T;
        let bool_d = Domain::Bool;
        let u8_d = Domain::Machine(MachineUIntWidth::U8);
        let u16_d = Domain::Machine(MachineUIntWidth::U16);
        let i32_d = Domain::Signed(MachineSIntWidth::I32);
        let b = |t: T| Box::new(t);
        let both = T::Ite {
            cond: b(T::And(b(T::Param(0)), b(T::Param(1)))),
            then: b(T::Int(1)),
            els: b(T::Int(0)),
        };
        let neither = T::Ite {
            cond: b(T::And(b(T::Param(0)), b(T::Param(1)))),
            then: b(T::Int(0)),
            els: b(T::Int(1)),
        };
        let cmp = |op, domain: &Domain, lit: i128| T::Cmp {
            op,
            domain: domain.clone(),
            left: b(T::Param(0)),
            right: b(T::Int(lit)),
        };
        let pick = |c: T, then: i128, els: i128| T::Ite {
            cond: b(c),
            then: b(T::Int(then)),
            els: b(T::Int(els)),
        };
        let one_u8 = pick(cmp(E6TreeCmp::Eq, &u8_d, 1), 7, 9);
        let other_u8 = pick(cmp(E6TreeCmp::Eq, &u8_d, 1), 9, 7);
        let neg_i32 = pick(cmp(E6TreeCmp::Lt, &i32_d, 0), 1, 0);
        let pos_i32 = pick(cmp(E6TreeCmp::Lt, &i32_d, 0), 0, 1);
        let gate = T::Ite { cond: b(T::Param(0)), then: b(T::Param(1)), els: b(T::Int(0)) };
        let other_gate = T::Ite { cond: b(T::Param(0)), then: b(T::Int(0)), els: b(T::Param(1)) };
        let eq_u8 = T::Cmp {
            op: E6TreeCmp::Eq,
            domain: u8_d.clone(),
            left: b(T::Param(0)),
            right: b(T::Param(1)),
        };
        let ne_u8 = T::Cmp {
            op: E6TreeCmp::Ne,
            domain: u8_d.clone(),
            left: b(T::Param(0)),
            right: b(T::Param(1)),
        };

        type Row<'a> = (&'a str, &'a [(&'a str, &'a str)], Vec<Domain>, Domain, &'a T, &'a T);
        let rows: [Row<'_>; 5] = [
            // THE FAILING SHAPE: uniform `bool` parameters, a `u8` result.
            (
                "result == spec(a, b)",
                &[("a", "bool"), ("b", "bool")],
                vec![bool_d.clone(), bool_d.clone()],
                u8_d.clone(),
                &both,
                &neither,
            ),
            // The same bug at two machine widths: `u8` parameter, `u16` result.
            ("result == spec(a)", &[("a", "u8")], vec![u8_d.clone()], u16_d.clone(), &one_u8, &other_u8),
            // Signed parameter, unsigned result.
            ("result == spec(a)", &[("a", "i32")], vec![i32_d.clone()], u8_d.clone(), &neg_i32, &pos_i32),
            // CONTROLS that already resolved, and must resolve to the same
            // carrier: mixed parameters (step 1 refuses as mixed, step 3
            // decides), and a `bool` result over `u8` parameters (the
            // decided-`bool` relation lane, which never reaches `atom_domain`).
            (
                "result == spec(a, b)",
                &[("a", "bool"), ("b", "u8")],
                vec![bool_d.clone(), u8_d.clone()],
                u8_d.clone(),
                &gate,
                &other_gate,
            ),
            (
                "result == spec(a, b)",
                &[("a", "u8"), ("b", "u8")],
                vec![u8_d.clone(), u8_d.clone()],
                bool_d.clone(),
                &eq_u8,
                &ne_u8,
            ),
        ];
        for (clause, params, domains, ret, body, other_body) in rows {
            let mut env = Environment::with_prelude();
            let t = tree_minted_table(
                &mut env,
                &[
                    ("k", &domains[..], &ret, body),
                    ("spec", &domains[..], &ret, body),
                    ("spec_other", &domains[..], &ret, other_body),
                ],
            );
            let row = format!("{params:?} -> {}", ret.rust_name());
            let goal = elaborate_ensures(clause, params, "k", &t)
                .unwrap_or_else(|e| panic!("{row}: `{clause}` must elaborate: {e}"));
            // `check_type`, the full check the compiler's ill-typed-goal gate
            // runs: `infer_type` alone reads an application's codomain without
            // checking its arguments, and accepts the `Eq Bool` over `UInt8`.
            let tc = clean_kernel::TypeChecker::new(&env);
            tc.check_type(&goal, &Expr::prop())
                .unwrap_or_else(|e| panic!("{row}: the goal must typecheck: {e:?}\n{goal}"));
            let (carrier, lhs, rhs) = eq_core(&goal);
            assert_eq!(carrier, ret.ty(), "{row}: the relation carrier must be the result's");
            assert!(tc.is_def_eq(&lhs, &rhs), "{row}: the same body must close by defeq");

            let other_clause = clause.replace("spec(", "spec_other(");
            let other = elaborate_ensures(&other_clause, params, "k", &t)
                .unwrap_or_else(|e| panic!("{row}: `{other_clause}` must elaborate: {e}"));
            assert!(
                tc.check_type(&other, &Expr::prop()).is_ok(),
                "{row}: the mutant goal must typecheck too"
            );
            let (_, l2, r2) = eq_core(&other);
            assert!(!tc.is_def_eq(&l2, &r2), "{row}: a different body must not close");
        }

        // NEGATIVES, each a named refusal rather than an ill-typed goal.
        let mut env = Environment::with_prelude();
        let two_bools = [bool_d.clone(), bool_d.clone()];
        let t = tree_minted_table(
            &mut env,
            &[
                ("k", &two_bools[..], &u8_d, &both),
                ("spec", &two_bools[..], &u8_d, &both),
                ("wide", &two_bools[..], &u16_d, &both),
                ("same8", &[u8_d.clone(), u8_d.clone()][..], &bool_d, &eq_u8),
                ("id8", &[u8_d.clone()][..], &u8_d, &T::Param(0)),
            ],
        );
        // An AMBIENT `bool` variable compared with a `u8` call is a genuinely
        // mixed comparison: the typed call does not excuse its sibling operand.
        let err = elaborate_goal_typed_with_facets(
            "flag == spec(a, b)",
            &[("flag", "bool"), ("a", "bool"), ("b", "bool")],
            &t,
        )
        .expect_err("a `bool` operand beside a `u8` call must fail closed");
        assert!(
            err.contains("declares its result at carrier `UInt8`, but the comparison is at carrier `Bool`"),
            "{err}"
        );
        // Two typed operands that RETURN different carriers disagree with each
        // other; the shared argument carrier must not reconcile them.
        let err = elaborate_ensures("result == wide(a, b)", &[("a", "bool"), ("b", "bool")], "k", &t)
            .expect_err("a `u8` result against a `u16` call must fail closed");
        assert!(err.contains("mixed domains in one comparison"), "{err}");
        // A CAST atom keeps step 1's domain and the cast's own refusal: outside
        // `ProofLift` it is `unsupported term shape`, to the byte, never the
        // "mixed domains" of the two casts' operands, which are not compared.
        let err = elaborate_ensures(
            "result as nat == wide(a, b) as nat",
            &[("a", "bool"), ("b", "bool")],
            "k",
            &t,
        )
        .expect_err("a cast is outside the strict clause fragment");
        assert!(err.contains("unsupported term shape"), "{err}");

        // A BARE call atom keeps step 1's domain for its arguments: the literal
        // beside a nested typed call takes `u8` from the variable inside it,
        // not `Bool` from what `same8` returns, and the goal typechecks.
        let goal = elaborate_goal_typed_with_facets("same8(id8(x), 3)", &[("x", "u8")], &t)
            .expect("a bare `-> bool` call with a literal argument must elaborate");
        clean_kernel::TypeChecker::new(&env)
            .check_type(&goal, &Expr::prop())
            .expect("the bare-call goal must typecheck");
    }

    /// TG15 (aterm's two-language gap plan, 2026-11-05), the whole matrix: for
    /// EVERY ordered pair of fixed-width parameter carriers E6 admits (`bool`,
    /// `u8`..`u64`, `i8`..`i64`; uniform and mixed) and every result carrier in
    /// the same set, `result == spec(a, b)` and `spec(a, b) == result` build a
    /// goal that typechecks, relates at the RESULT's carrier, closes by
    /// definitional equality against a mint of the same body and does not
    /// close against a mutant (the arms, or the connective, changed). `!=` and,
    /// for an integer result, `<=` must typecheck too. The regression above
    /// pins five cells of this; this pins all 729, so a carrier rule that is
    /// right for the cells someone thought of and wrong for another fails here.
    /// Negative control: with `step_one_result_carrier_conflict`'s `Some` arm
    /// returning step 1's domain again, the uniform cells whose parameter and
    /// result carriers differ fail the `check_type` assertion.
    #[test]
    fn every_fixed_width_parameter_and_result_mix_relates_at_the_result_carrier() {
        use E6TreeTerm as T;
        let b = |t: T| Box::new(t);
        let carriers: [Domain; 9] = [
            Domain::Bool,
            Domain::Machine(MachineUIntWidth::U8),
            Domain::Machine(MachineUIntWidth::U16),
            Domain::Machine(MachineUIntWidth::U32),
            Domain::Machine(MachineUIntWidth::U64),
            Domain::Signed(MachineSIntWidth::I8),
            Domain::Signed(MachineSIntWidth::I16),
            Domain::Signed(MachineSIntWidth::I32),
            Domain::Signed(MachineSIntWidth::I64),
        ];
        // Parameter `i` read as a `bool` at its own carrier.
        let flag = |i: usize, d: &Domain| -> T {
            if *d == Domain::Bool {
                T::Param(i)
            } else {
                T::Cmp {
                    op: E6TreeCmp::Eq,
                    domain: d.clone(),
                    left: b(T::Param(i)),
                    right: b(T::Int(1)),
                }
            }
        };
        let mut cells = 0usize;
        for p in &carriers {
            for q in &carriers {
                let params = [("a", p.rust_name()), ("b", q.rust_name())];
                let domains = [p.clone(), q.clone()];
                let mut env = Environment::with_prelude();
                for (ri, ret) in carriers.iter().enumerate() {
                    let both = T::And(b(flag(0, p)), b(flag(1, q)));
                    // An integer result picks between two literals (negative for
                    // a signed carrier); a `bool` result is the decision itself.
                    let (body, mutant) = if *ret == Domain::Bool {
                        (both.clone(), T::Or(b(flag(0, p)), b(flag(1, q))))
                    } else {
                        let (x, y) = if matches!(ret, Domain::Signed(_)) { (-3, 5) } else { (7, 9) };
                        let pick = |x: i128, y: i128| T::Ite {
                            cond: b(both.clone()),
                            then: b(T::Int(x)),
                            els: b(T::Int(y)),
                        };
                        (pick(x, y), pick(y, x))
                    };
                    let (k, spec, other) =
                        (format!("k{ri}"), format!("spec{ri}"), format!("other{ri}"));
                    let t = tree_minted_table(
                        &mut env,
                        &[
                            (k.as_str(), &domains[..], ret, &body),
                            (spec.as_str(), &domains[..], ret, &body),
                            (other.as_str(), &domains[..], ret, &mutant),
                        ],
                    );
                    let tc = clean_kernel::TypeChecker::new(&env);
                    let cell =
                        format!("({}, {}) -> {}", p.rust_name(), q.rust_name(), ret.rust_name());
                    let build = |clause: &str| {
                        let goal = elaborate_ensures(clause, &params, &k, &t)
                            .unwrap_or_else(|e| panic!("{cell}: `{clause}` must elaborate: {e}"));
                        tc.check_type(&goal, &Expr::prop()).unwrap_or_else(|e| {
                            panic!("{cell}: `{clause}` must typecheck: {e:?}\n{goal}")
                        });
                        goal
                    };
                    for (same, mutated) in [
                        (format!("result == {spec}(a, b)"), format!("result == {other}(a, b)")),
                        (format!("{spec}(a, b) == result"), format!("{other}(a, b) == result")),
                    ] {
                        let (carrier, lhs, rhs) = eq_core(&build(&same));
                        assert_eq!(carrier, ret.ty(), "{cell}: `{same}` must relate at the result's carrier");
                        assert!(tc.is_def_eq(&lhs, &rhs), "{cell}: `{same}` must close by defeq");
                        let (carrier, lhs, rhs) = eq_core(&build(&mutated));
                        assert_eq!(
                            carrier,
                            ret.ty(),
                            "{cell}: `{mutated}` must relate at the result's carrier"
                        );
                        assert!(!tc.is_def_eq(&lhs, &rhs), "{cell}: `{mutated}` must not close");
                    }
                    let _ne = build(&format!("result != {other}(a, b)"));
                    if *ret != Domain::Bool {
                        let _le = build(&format!("result <= {spec}(a, b)"));
                    }
                    cells += 1;
                }
            }
        }
        assert_eq!(cells, 729, "every parameter pair against every result carrier");

        // A typed call NESTED in a typed call's argument, each at its own
        // carrier: `(bool, bool) -> u8` inside `u8 -> u16`, related at `u16`.
        let (bool_d, u8_d, u16_d) = (
            Domain::Bool,
            Domain::Machine(MachineUIntWidth::U8),
            Domain::Machine(MachineUIntWidth::U16),
        );
        let both = T::And(b(T::Param(0)), b(T::Param(1)));
        let inner = T::Ite { cond: b(both.clone()), then: b(T::Int(1)), els: b(T::Int(0)) };
        let outer = T::Ite { cond: b(flag(0, &u8_d)), then: b(T::Int(7)), els: b(T::Int(9)) };
        let k = T::Ite { cond: b(both), then: b(T::Int(7)), els: b(T::Int(9)) };
        let two_bools = [bool_d.clone(), bool_d];
        let mut env = Environment::with_prelude();
        let t = tree_minted_table(
            &mut env,
            &[
                ("k", &two_bools[..], &u16_d, &k),
                ("inner", &two_bools[..], &u8_d, &inner),
                ("outer", &[u8_d.clone()][..], &u16_d, &outer),
            ],
        );
        let goal = elaborate_ensures(
            "result == outer(inner(a, b))",
            &[("a", "bool"), ("b", "bool")],
            "k",
            &t,
        )
        .expect("a nested typed call must elaborate");
        let tc = clean_kernel::TypeChecker::new(&env);
        tc.check_type(&goal, &Expr::prop()).expect("the nested goal must typecheck");
        assert_eq!(eq_core(&goal).0, u16_d.ty(), "the nested relation is at the outer call's result");
    }

    /// TG15, the cast half: a cast INSIDE a typed call's argument list does not
    /// keep the relation at step 1's variable domain. `bucket_spec(x as nat)` is
    /// a `UInt8` result whatever `x` is, so on `fn bucket(x: u32) -> u8` the
    /// E9 lane (`ProofLift`) relates two `UInt8` calls; keeping step 1's
    /// `UInt32` (the exemption d96de26814 gave every atom with a cast in it)
    /// built `@Eq UInt32` over them and the kernel refused the goal as
    /// ill-typed, TG15's symptom. Measured on origin/main e88d030c4a before the
    /// fix: `TypeMismatch { expected: UInt32, inferred: UInt8 }`. Strict mode
    /// keeps its `unsupported term shape` refusal, and a `u32` operand beside
    /// the `u8` call is still a mixed comparison.
    #[test]
    fn a_cast_inside_a_typed_call_argument_does_not_type_the_relation() {
        use E6TreeTerm as T;
        let u8_d = Domain::Machine(MachineUIntWidth::U8);
        let u32_d = Domain::Machine(MachineUIntWidth::U32);
        let cert = || FacetStatus::Certified { evidence: "test".into() };
        let mut env = Environment::with_prelude();
        // pub fn bucket(x: u32) -> u8 { 7 } and pub fn small(x: u32) -> bool { x < 5 }
        let small_body = T::Cmp {
            op: E6TreeCmp::Lt,
            domain: u32_d.clone(),
            left: Box::new(T::Param(0)),
            right: Box::new(T::Int(5)),
        };
        let mut t = tree_minted_table(
            &mut env,
            &[
                ("bucket", &[u32_d.clone()][..], &u8_d, &T::Int(7)),
                ("small", &[u32_d.clone()][..], &Domain::Bool, &small_body),
            ],
        );
        // clean { def bucket_spec (n : Nat) : UInt8 := 7 } plus a mutant returning 9,
        // admitted with the carriers audited_island_definition_admission records.
        for (name, kernel_const, value) in
            [("bucket_spec", "bucket_spec_def", 7u128), ("bucket_other", "bucket_other_def", 9u128)]
        {
            env.add_decl(Declaration::Definition {
                name: Name::from_string(kernel_const),
                level_params: vec![],
                type_: Expr::arrow(Domain::Nat.ty(), u8_d.ty()),
                value: Expr::lam(
                    BinderInfo::Default,
                    Domain::Nat.ty(),
                    u8_d.numeral(value).expect("the literal fits UInt8"),
                ),
                is_reducible: true,
            })
            .expect("the island-style definition must be well-typed");
            t.insert(
                name,
                FnFacets { pure: cert(), total: cert(), deterministic: cert(), no_panic: cert() },
            );
            t.admit(
                name,
                Admission::reflected(kernel_const, 1).with_declared_signature(
                    Some(u8_d.clone()),
                    Some(DeclaredCarriers::of_domains(&[Domain::Nat], &u8_d)),
                ),
            );
        }
        let lifted = |clause: &str, self_fn: &str, result_ty: &str| {
            elaborate_ensures_in(
                clause,
                &[("x", "u32")],
                self_fn,
                &t,
                &ProofClauseInputs::proof_lift(Some(result_ty)),
            )
            .unwrap_or_else(|e| panic!("`{clause}` must elaborate: {e}"))
            .goal
        };
        let tc = clean_kernel::TypeChecker::new(&env);
        for clause in ["result == bucket_spec(x as nat)", "bucket_spec(x as nat) == result"] {
            let goal = lifted(clause, "bucket", "u8");
            tc.check_type(&goal, &Expr::prop())
                .unwrap_or_else(|e| panic!("`{clause}` must typecheck: {e:?}\n{goal}"));
            let (carrier, lhs, rhs) = eq_core(&goal);
            assert_eq!(carrier, u8_d.ty(), "`{clause}` relates two UInt8 call results at UInt8");
            assert!(tc.is_def_eq(&lhs, &rhs), "`{clause}`: the same body must close by defeq");
            let mutant = clause.replace("bucket_spec(", "bucket_other(");
            let other = lifted(&mutant, "bucket", "u8");
            tc.check_type(&other, &Expr::prop())
                .unwrap_or_else(|e| panic!("`{mutant}` must typecheck: {e:?}\n{other}"));
            let (_, l2, r2) = eq_core(&other);
            assert!(!tc.is_def_eq(&l2, &r2), "`{mutant}`: a different body must not close");
        }
        // The decided-bool lane reaches the same exemption through
        // `elab_bool_term`'s comparison arm.
        let goal = lifted("result == (bucket_spec(x as nat) < 5)", "small", "bool");
        tc.check_type(&goal, &Expr::prop())
            .unwrap_or_else(|e| panic!("the decided comparison must typecheck: {e:?}\n{goal}"));
        assert_eq!(eq_core(&goal).0, Domain::Bool.ty());
        // NEGATIVE CONTROLS. Strict mode reads no cast: still refused by the
        // pre-existing message, never built at any carrier.
        let err = elaborate_ensures("result == bucket_spec(x as nat)", &[("x", "u32")], "bucket", &t)
            .expect_err("a cast is outside the strict clause fragment");
        assert!(err.contains("unsupported term shape"), "{err}");
        // An AMBIENT `u32` operand beside the `u8` call is a genuinely mixed
        // comparison; the cast inside the call's argument does not excuse it.
        let err = elaborate_ensures_in(
            "x == bucket_spec(x as nat)",
            &[("x", "u32")],
            "bucket",
            &t,
            &ProofClauseInputs::proof_lift(Some("u8")),
        )
        .expect_err("a `u32` operand against a `u8` call must fail closed");
        assert!(err.contains("UInt8") && err.contains("UInt32"), "{err}");
    }

    /// TG15, the variable-free half: an atom with no clause variable (a
    /// nullary kernel's `result`) takes its domain from AMBIENT evidence, so a
    /// typed call contributes the result it declares and nothing from inside
    /// its argument list. `result == widen(g())` on `fn k() -> u16` relates two
    /// `UInt16` results; reading `g`'s `UInt8` out of `widen`'s argument refused
    /// it as "mixed domains" (measured on origin/main e88d030c4a before the
    /// fix). An ambient `u8` operand against the `u16` result is still refused.
    #[test]
    fn a_variable_free_relation_takes_no_evidence_from_a_typed_calls_arguments() {
        use E6TreeTerm as T;
        let u8_d = Domain::Machine(MachineUIntWidth::U8);
        let u16_d = Domain::Machine(MachineUIntWidth::U16);
        let nullary: [Domain; 0] = [];
        let mut env = Environment::with_prelude();
        let t = tree_minted_table(
            &mut env,
            &[
                // fn k() -> u16 { 7 }
                ("k", &nullary[..], &u16_d, &T::Int(7)),
                // def g : UInt8 := 7
                ("g", &nullary[..], &u8_d, &T::Int(7)),
                // def widen (b : UInt8) : UInt16 := 7, and a mutant returning 9
                ("widen", &[u8_d.clone()][..], &u16_d, &T::Int(7)),
                ("widen_other", &[u8_d.clone()][..], &u16_d, &T::Int(9)),
            ],
        );
        let tc = clean_kernel::TypeChecker::new(&env);
        for (clause, inputs) in [
            ("result == widen(g())", ProofClauseInputs::strict()),
            ("widen(g()) == result", ProofClauseInputs::strict()),
            ("result == widen(7u8)", ProofClauseInputs::proof_lift(Some("u16"))),
        ] {
            let goal = elaborate_ensures_in(clause, &[], "k", &t, &inputs)
                .unwrap_or_else(|e| panic!("`{clause}` must elaborate: {e}"))
                .goal;
            tc.check_type(&goal, &Expr::prop())
                .unwrap_or_else(|e| panic!("`{clause}` must typecheck: {e:?}\n{goal}"));
            let (carrier, lhs, rhs) = eq_core(&goal);
            assert_eq!(carrier, u16_d.ty(), "`{clause}` relates the two UInt16 results at UInt16");
            assert!(tc.is_def_eq(&lhs, &rhs), "`{clause}` must close by defeq");
            let mutant = clause.replace("widen(", "widen_other(");
            let other = elaborate_ensures_in(&mutant, &[], "k", &t, &inputs)
                .unwrap_or_else(|e| panic!("`{mutant}` must elaborate: {e}"))
                .goal;
            tc.check_type(&other, &Expr::prop())
                .unwrap_or_else(|e| panic!("`{mutant}` must typecheck: {e:?}\n{other}"));
            let (_, l2, r2) = eq_core(&other);
            assert!(!tc.is_def_eq(&l2, &r2), "`{mutant}` must not close");
        }
        // Control that must stay red: an AMBIENT u8 operand against the u16 result.
        let err = elaborate_ensures("result == g()", &[], "k", &t)
            .expect_err("a u16 result against a u8 call must fail closed");
        assert!(err.contains("mixed domains"), "{err}");
    }

    /// TG15, the Option half: parentheses around an `Option<iN>` self-call do
    /// not move the relation off the Option carrier. `(result) == Some(a)` was
    /// typed from the constructor's argument (`BitVec 8`) and refused against
    /// the self-call's `Option (BitVec 8)` result (measured on origin/main
    /// e88d030c4a before the fix); it now builds the same goal as the bare
    /// spelling.
    #[test]
    fn a_parenthesized_option_self_call_keeps_the_option_relation() {
        let i8_d = Domain::Signed(MachineSIntWidth::I8);
        let mut env = Environment::with_prelude();
        let adm = admit_checked_arithmetic_function(
            &mut env,
            "k_def",
            &[i8_d.clone(), i8_d.clone()],
            CheckedArithOp::Add,
            MachineSIntWidth::I8,
            CmpOperand::Param(0),
            CmpOperand::Param(1),
        )
        .expect("the checked-add mint must admit");
        let t = admitted_table("k", adm);
        let params: &[(&str, &str)] = &[("a", "i8"), ("b", "i8")];
        let plain = elaborate_ensures("result == Some(a)", params, "k", &t)
            .expect("control: the unparenthesized clause elaborates");
        let tc = clean_kernel::TypeChecker::new(&env);
        for clause in ["(result) == Some(a)", "((result)) == Some(a)", "Some(a) == (result)"] {
            let goal = elaborate_ensures(clause, params, "k", &t)
                .unwrap_or_else(|e| panic!("`{clause}` must elaborate: {e}"));
            tc.check_type(&goal, &Expr::prop())
                .unwrap_or_else(|e| panic!("`{clause}` must typecheck: {e:?}\n{goal}"));
            assert_eq!(
                eq_core(&goal).0,
                Domain::OptionSigned(MachineSIntWidth::I8).ty(),
                "`{clause}` relates at the Option carrier"
            );
        }
        let paren = elaborate_ensures("(result) == Some(a)", params, "k", &t)
            .unwrap_or_else(|e| panic!("`(result) == Some(a)` must elaborate: {e}"));
        assert_eq!(paren, plain, "parentheses do not make a different clause");
    }

    /// TG15 open item 1 (`docs/validation/2026-11-06-tg15-result-carrier.md`):
    /// a typed call NESTED in a typed call's argument whose result no
    /// declaration names a domain for. `def g (b : Bool) : BitVec 16` records
    /// carriers and no return domain (`BitVec 16` is `i16` and a 16-bit
    /// pointer-sized integer alike), so the argument fallback gave `g(a)` the
    /// relation's `u8` and the carrier check refused `f(g(a))` ("declares
    /// parameter 0 at carrier `BitVec 16`, but the argument is a `u8` term").
    /// The two DECLARATIONS are compared now and no domain is read off either: a
    /// nested result at another carrier is refused, a literal inside the nested
    /// call is still not typed from its `BitVec 16` slot, and a nested call with
    /// no carrier record keeps the old refusal.
    #[test]
    fn a_nested_call_with_no_result_domain_is_checked_by_its_declared_carrier() {
        use E6TreeTerm as T;
        let b = |t: T| Box::new(t);
        let bool_d = Domain::Bool;
        let u8_d = Domain::Machine(MachineUIntWidth::U8);
        let i16_d = Domain::Signed(MachineSIntWidth::I16);
        let i32_d = Domain::Signed(MachineSIntWidth::I32);
        let pick = |then: i128, els: i128| T::Ite {
            cond: b(T::Cmp {
                op: E6TreeCmp::Eq,
                domain: i16_d.clone(),
                left: b(T::Param(0)),
                right: b(T::Int(1)),
            }),
            then: b(T::Int(then)),
            els: b(T::Int(els)),
        };
        let (f_body, f_mutant) = (pick(7, 9), pick(9, 7));
        let mut env = Environment::with_prelude();
        // def f (x : BitVec 16) : UInt8 := if x = 1 then 7 else 9, and the
        // arms-swapped mutant: the carriers and the `UInt8` return domain an
        // island admission records for that declaration.
        let mut t = tree_minted_table(
            &mut env,
            &[
                ("f", &[i16_d.clone()][..], &u8_d, &f_body),
                ("f_other", &[i16_d.clone()][..], &u8_d, &f_mutant),
            ],
        );
        let cert = || FacetStatus::Certified { evidence: "test".into() };
        let facets =
            || FnFacets { pure: cert(), total: cert(), deterministic: cert(), no_panic: cert() };
        // def g (b : Bool) : BitVec 16 := if b then 1 else 0, `h` the same at
        // BitVec 32 and wrap (x : BitVec 16) : BitVec 16 := x, admitted the way
        // the island admission records a `BitVec` codomain: carriers, and NO
        // return domain.
        let flag_bits = T::Ite { cond: b(T::Param(0)), then: b(T::Int(1)), els: b(T::Int(0)) };
        let identity = T::Param(0);
        for (name, params, ret, body) in [
            ("g", [bool_d.clone()], &i16_d, &flag_bits),
            ("h", [bool_d.clone()], &i32_d, &flag_bits),
            ("wrap", [i16_d.clone()], &i16_d, &identity),
        ] {
            let minted =
                admit_e6_tree_function(&mut env, &format!("{name}_def"), &params, ret, body)
                    .unwrap_or_else(|e| panic!("`{name}` must mint: {e}"));
            t.insert(name, facets());
            t.admit(
                name,
                minted.with_declared_signature(
                    None,
                    Some(DeclaredCarriers::of_domains(&params, ret)),
                ),
            );
        }
        // fn k(a: bool) -> u8 { f(g(a)) }: its import is the composition.
        let app =
            |callee: &str, x: Expr| Expr::app(Expr::const_(Name::from_string(callee), vec![]), x);
        env.add_decl(Declaration::Definition {
            name: Name::from_string("k_def"),
            level_params: vec![],
            type_: Expr::arrow(bool_d.ty(), u8_d.ty()),
            value: Expr::lam(
                BinderInfo::Default,
                bool_d.ty(),
                app("f_def", app("g_def", Expr::bvar(0))),
            ),
            is_reducible: true,
        })
        .expect("the composed import is well-typed");
        t.insert("k", facets());
        t.admit(
            "k",
            Admission::reflected("k_def", 1).with_declared_signature(
                Some(u8_d.clone()),
                Some(DeclaredCarriers::of_domains(std::slice::from_ref(&bool_d), &u8_d)),
            ),
        );
        let params: &[(&str, &str)] = &[("a", "bool")];
        let tc = clean_kernel::TypeChecker::new(&env);
        for (same, mutated) in [
            ("result == f(g(a))", "result == f_other(g(a))"),
            ("f(g(a)) == result", "f_other(g(a)) == result"),
        ] {
            let goal = elaborate_ensures(same, params, "k", &t)
                .unwrap_or_else(|e| panic!("`{same}` must elaborate: {e}"));
            tc.check_type(&goal, &Expr::prop())
                .unwrap_or_else(|e| panic!("`{same}` must typecheck: {e:?}\n{goal}"));
            let (carrier, lhs, rhs) = eq_core(&goal);
            assert_eq!(carrier, u8_d.ty(), "`{same}` relates at the outer call's result");
            assert!(tc.is_def_eq(&lhs, &rhs), "`{same}` must close by defeq");
            let other = elaborate_ensures(mutated, params, "k", &t)
                .unwrap_or_else(|e| panic!("`{mutated}` must elaborate: {e}"));
            tc.check_type(&other, &Expr::prop())
                .unwrap_or_else(|e| panic!("`{mutated}` must typecheck: {e:?}\n{other}"));
            let (_, l2, r2) = eq_core(&other);
            assert!(!tc.is_def_eq(&l2, &r2), "`{mutated}` must not close");
        }
        // A nested result at ANOTHER carrier is refused, naming both.
        let err = elaborate_ensures("result == f(h(a))", params, "k", &t)
            .expect_err("a `BitVec 32` result at a `BitVec 16` parameter must fail closed");
        assert!(
            err.contains("declares parameter 0 at carrier `BitVec 16`")
                && err.contains("return carrier `BitVec 32`"),
            "{err}"
        );
        // A literal inside the nested call takes no domain from the `BitVec 16`
        // slot it fills (I0): `3` keeps the relation's `u8` and `wrap`'s own
        // declared parameter refuses it.
        let err = elaborate_ensures("result == f(wrap(3))", params, "k", &t)
            .expect_err("a literal is never typed from a declared `BitVec` carrier");
        assert!(
            err.contains("admitted `wrap` declares parameter 0 at carrier `BitVec 16`"),
            "{err}"
        );
        // A nested call with NO carrier record is not a typed call: its
        // arguments are read as before and the original refusal stands.
        let mut untyped = t.clone();
        untyped.admit("g", Admission::reflected("g_def", 1));
        let err = elaborate_ensures("result == f(g(a))", params, "k", &untyped)
            .expect_err("a nested call with no carrier record must fail closed");
        assert!(err.contains("admitted `f` declares parameter 0 at carrier `BitVec 16`"), "{err}");
    }

    /// TG15 open item 3: equal carriers are not equal domains. `u128` and
    /// `i128` share `BitVec 128`, so the carrier check passed `fn k(a: u128) ->
    /// i128 { -1 }` with `ensures result >= 0` at step 1's `u128`, the
    /// parameter's UNSIGNED order over a signed result: a goal true of every
    /// input, for a postcondition false of every input. The relation now reads
    /// the result the way the callee's recorded return domain does, so the goal
    /// is the very one an `i128` binder builds over the same import, and an
    /// ambient `u128` operand beside the `i128` result is refused. Readings,
    /// not names, are compared: an `isize` relation on a 64-bit target still
    /// reads an `i64` result.
    #[test]
    fn a_shared_carrier_does_not_decide_how_a_result_is_read() {
        use E6TreeTerm as T;
        let i128_d = Domain::Signed(MachineSIntWidth::I128);
        let i64_d = Domain::Signed(MachineSIntWidth::I64);
        let (minus_one, identity) = (T::Int(-1), T::Param(0));
        let mut env = Environment::with_prelude();
        let t = tree_minted_table(
            &mut env,
            &[
                // fn k(a: u128) -> i128 { -1 }, minted over the parameter it ignores.
                ("k", &[Domain::U128][..], &i128_d, &minus_one),
                // fn id(x: i64) -> i64 { x }
                ("id", &[i64_d.clone()][..], &i64_d, &identity),
            ],
        );
        let tc = clean_kernel::TypeChecker::new(&env);
        for clause in ["result >= 0", "0 <= result", "result < 1"] {
            let signed = elaborate_ensures(clause, &[("a", "i128")], "k", &t)
                .unwrap_or_else(|e| panic!("`{clause}` over an `i128` binder must elaborate: {e}"));
            let goal = elaborate_ensures(clause, &[("a", "u128")], "k", &t)
                .unwrap_or_else(|e| panic!("`{clause}` over a `u128` binder must elaborate: {e}"));
            tc.check_type(&goal, &Expr::prop())
                .unwrap_or_else(|e| panic!("`{clause}` must typecheck: {e:?}\n{goal}"));
            assert_eq!(goal, signed, "`{clause}` must read the `i128` result in signed order");
        }
        let err = elaborate_ensures("result >= a", &[("a", "u128")], "k", &t)
            .expect_err("a `u128` operand against an `i128` result must fail closed");
        assert!(
            err.contains("returns a `i128`") && err.contains("comparison is at `u128`"),
            "{err}"
        );
        let pointer = elaborate_ensures("result >= x", &[("x", "isize64")], "id", &t)
            .expect("an `isize` relation reads an `i64` result");
        let fixed = elaborate_ensures("result >= x", &[("x", "i64")], "id", &t)
            .expect("control: the `i64` spelling elaborates");
        assert_eq!(pointer, fixed, "the two spellings read one value and build one goal");
    }

    /// The reading check above compares a call's recorded result with the
    /// domain a RELATION is built at. A bare call atom is no relation:
    /// `atom_domain` hands its domain to `elab_term` as the domain of the
    /// call's ARGUMENTS, so `p(widen(flag), x)` (read as `p(..) = true`) types
    /// `x` and `widen`'s result at `u8` and never reads `p`'s `bool` result
    /// there. `p` records its result and no carriers (an island whose telescope
    /// the carrier reader cannot read), so its arguments are operands of the
    /// atom; step 1 sees `flag` and `x` and refuses as mixed, and step 3 types
    /// the atom from `x`. Without the bare-call exemption the reading check
    /// refused this well-typed clause, which the carrier check had accepted,
    /// with "`p` returns a `bool` ... the comparison is at `u8`".
    #[test]
    fn a_bare_call_atom_is_not_read_at_its_argument_domain() {
        use E6TreeTerm as T;
        let b = |t: T| Box::new(t);
        let (bool_d, u8_d) = (Domain::Bool, Domain::Machine(MachineUIntWidth::U8));
        let mut env = Environment::with_prelude();
        let flag_bits = T::Ite { cond: b(T::Param(0)), then: b(T::Int(1)), els: b(T::Int(0)) };
        let mut t =
            tree_minted_table(&mut env, &[("widen", &[bool_d.clone()][..], &u8_d, &flag_bits)]);
        let same = T::Cmp {
            op: E6TreeCmp::Eq,
            domain: u8_d.clone(),
            left: b(T::Param(0)),
            right: b(T::Param(1)),
        };
        let minted = admit_e6_tree_function(
            &mut env,
            "p_def",
            &[u8_d.clone(), u8_d.clone()],
            &bool_d,
            &same,
        )
        .expect("the `u8, u8 -> bool` tree must mint");
        let cert = || FacetStatus::Certified { evidence: "test".into() };
        t.insert(
            "p",
            FnFacets { pure: cert(), total: cert(), deterministic: cert(), no_panic: cert() },
        );
        t.admit("p", minted.with_declared_signature(Some(bool_d.clone()), None));
        let tc = clean_kernel::TypeChecker::new(&env);
        for clause in ["p(widen(flag), x)", "(p(widen(flag), x))", "!p(widen(flag), x)"] {
            let goal =
                elaborate_goal_typed_with_facets(clause, &[("flag", "bool"), ("x", "u8")], &t)
                    .unwrap_or_else(|e| panic!("`{clause}` must elaborate: {e}"));
            tc.check_type(&goal, &Expr::prop())
                .unwrap_or_else(|e| panic!("`{clause}` must typecheck: {e:?}\n{goal}"));
        }
    }

    /// E6 widening increment 5, clause half: a clause comparing an admitted
    /// `-> bool` function against the NESTED COMPARISON it computes elaborates
    /// to an `Eq Bool` whose two sides are DEFINITIONALLY EQUAL — which is what
    /// makes `ensures result == (a <= b)` close by `Eq.refl` with no citation.
    ///
    /// This is the single load-bearing property of the whole increment: the
    /// clause's `(a <= b)` must produce the very term
    /// [`admit_comparison_function`] minted, not merely an equivalent one. An
    /// `Iff`, a `Nat.ble`, or any other equally-true encoding would leave the
    /// two sides stuck at different head constants and no reducibility setting
    /// could bridge them (the select-encoding iota lesson, 2026-07-25).
    #[test]
    fn a_nested_comparison_clause_is_defeq_to_the_comparison_mint() {
        for (rust_ty, dom) in [
            ("i64", Domain::Signed(MachineSIntWidth::I64)),
            ("u64", Domain::Machine(MachineUIntWidth::U64)),
            ("i8", Domain::Signed(MachineSIntWidth::I8)),
        ] {
            let mut env = Environment::with_prelude();
            let adm = admit_comparison_function(
                &mut env,
                "le_def",
                &[dom.clone(), dom.clone()],
                SelectCmp::Le,
                CmpOperand::Param(0),
                CmpOperand::Param(1),
            )
            .expect("the comparison mint must admit");
            assert_eq!(
                adm.return_domain().cloned(),
                Some(Domain::Bool),
                "the comparison mint must record a Bool return domain"
            );
            let t = admitted_table("le", adm);
            let vt: &[(&str, &str)] = &[("a", rust_ty), ("b", rust_ty)];

            let goal = elaborate_goal_typed_with_facets("le(a, b) == (a <= b)", vt, &t)
                .unwrap_or_else(|e| {
                    panic!("`le(a, b) == (a <= b)` at {rust_ty} must elaborate: {e}")
                });
            // The goal TYPECHECKS — the gate `reject_untyped_goal` enforces
            // downstream, asserted here at the source.
            let tc = clean_kernel::TypeChecker::new(&env);
            let ty = tc
                .infer_type(&goal)
                .unwrap_or_else(|e| panic!("the {rust_ty} goal must be well-typed: {e:?}"));
            assert!(tc.is_def_eq(&ty, &Expr::sort(Level::zero())), "the goal must be a Prop");

            let (carrier, lhs, rhs) = eq_core(&goal);
            assert_eq!(
                carrier,
                Expr::const_(Name::from_string("Bool"), vec![]),
                "the relation carrier must be Bool at {rust_ty}, not the operands' carrier"
            );
            assert!(
                tc.is_def_eq(&lhs, &rhs),
                "at {rust_ty} the minted body and the clause's decided comparison must be \
                 definitionally equal — got lhs={lhs:?} rhs={rhs:?}"
            );

            // `>=` normalizes by operand swap onto the SAME `Le` mint.
            let swapped = elaborate_goal_typed_with_facets("le(a, b) == (b >= a)", vt, &t)
                .expect("`>=` must normalize by operand swap");
            let (_, l2, r2) = eq_core(&swapped);
            assert!(tc.is_def_eq(&l2, &r2), "`b >= a` must be the same decision as `a <= b`");

            // The reversed comparison is NOT defeq — the encoding distinguishes
            // `a <= b` from `b <= a`, so a positive test alone cannot pass by
            // accident.
            let reversed = elaborate_goal_typed_with_facets("le(a, b) == (b <= a)", vt, &t)
                .expect("the reversed clause must still elaborate");
            let (_, l3, r3) = eq_core(&reversed);
            assert!(!tc.is_def_eq(&l3, &r3), "`b <= a` must NOT be the `a <= b` decision");
        }
    }

    /// The other spelling the guard layer reaches for: an admitted `-> bool`
    /// call standing alone as a PROPOSITION, read as `f(a, b) = true` — the
    /// same reading a bare `bool` binding already gets. Everything else in
    /// proposition position keeps failing closed.
    #[test]
    fn an_admitted_bool_call_is_a_proposition_and_others_still_fail_closed() {
        let dom = Domain::Signed(MachineSIntWidth::I64);
        let mut env = Environment::with_prelude();
        let le = admit_comparison_function(
            &mut env,
            "le_def",
            &[dom.clone(), dom.clone()],
            SelectCmp::Le,
            CmpOperand::Param(0),
            CmpOperand::Param(1),
        )
        .expect("comparison mint");
        let min2 = admit_select_function(
            &mut env,
            "min2_def",
            &[dom.clone(), dom.clone()],
            SelectCmp::Lt,
            0,
            1,
            0,
            1,
        )
        .expect("select mint");
        assert_eq!(min2.return_domain().cloned(), Some(dom.clone()), "the select mint records its carrier");

        let mut t = admitted_table("le", le);
        let cert = || FacetStatus::Certified { evidence: "test".into() };
        t.insert(
            "min2",
            FnFacets { pure: cert(), total: cert(), deterministic: cert(), no_panic: cert() },
        );
        t.admit("min2", min2);
        let vt: &[(&str, &str)] = &[("a", "i64"), ("b", "i64")];
        let tc = clean_kernel::TypeChecker::new(&env);

        // POSITIVE: `!le(a, b) || a <= b` — the guard-layer spelling.
        let goal = elaborate_goal_typed_with_facets("!le(a, b) || a <= b", vt, &t)
            .expect("a bool-returning call in proposition position must elaborate");
        let ty = tc.infer_type(&goal).expect("the goal must be well-typed");
        assert!(tc.is_def_eq(&ty, &Expr::sort(Level::zero())), "must be a Prop");
        // EXACT TERM PIN: `∀ (a b : BitVec 64), Or (Not (le_def a b = true))
        // (Nat.le (key a) (key b))`. The `= true` reading is the whole point of
        // the arm, so it is asserted as a term rather than by grepping Debug
        // output (a `Bool.true` const prints as its name SEGMENTS, so the
        // obvious substring check silently passes on nothing).
        let call = Expr::apps(
            Expr::const_(Name::from_string("le_def"), vec![]),
            [Expr::bvar(1), Expr::bvar(0)],
        );
        let expected = Expr::pi(
            BinderInfo::Default,
            dom.ty(),
            Expr::pi(
                BinderInfo::Default,
                dom.ty(),
                connective(
                    "Or",
                    Expr::app(
                        Expr::const_(Name::from_string("Not"), vec![]),
                        Domain::Bool.eq(call, Domain::Bool.bool_lit(true).unwrap()),
                    ),
                    dom.cmp("le", Expr::bvar(1), Expr::bvar(0)),
                ),
            ),
        );
        assert_eq!(goal, expected, "the prop-position reading drifted from `f(a, b) = true`");

        // NEGATIVE 1: an admitted call that does NOT return bool stays outside
        // the fragment in proposition position.
        let err = elaborate_goal_typed_with_facets("min2(a, b)", vt, &t).unwrap_err();
        assert!(err.contains("fail closed"), "a non-bool admitted call must fail closed: {err}");

        // NEGATIVE 2: an UNADMITTED `-> bool` callee keeps the E6 diagnostic.
        let err = elaborate_goal_typed_with_facets("ge(a, b)", vt, &t).unwrap_err();
        assert!(err.contains("no diagnostic E6 facet record exists"), "{err}");

        // NEGATIVE 3: `bool` is unordered — a decided bool side may not be
        // compared with `<=`, and the reason says so rather than blaming a
        // domain mix that does not exist.
        let err = elaborate_goal_typed_with_facets("le(a, b) <= (a <= b)", vt, &t).unwrap_err();
        assert!(err.contains("not ordered"), "{err}");

        // NEGATIVE 4: a genuinely mixed comparison still fails closed, with the
        // mixed-domain reason preserved.
        let err =
            elaborate_goal_typed_with_facets("a == (b <= b)", &[("a", "i64"), ("b", "i64")], &t)
                .unwrap_err();
        assert!(err.contains("mixed domains in one comparison"), "{err}");

        // NEGATIVE 5: a variable-free comparison has no decidable carrier
        // (it defaults to `Nat`), so it is refused rather than decided.
        let err = elaborate_goal_typed_with_facets("le(a, b) == (1 <= 2)", vt, &t).unwrap_err();
        assert!(err.contains("comparison decisions require"), "{err}");
    }

    /// E6 widening increment 7, mint half: the bool-binary mint computes the
    /// right Bool on concrete inputs (a semantic oracle via `is_def_eq`), and
    /// every out-of-fragment shape fails closed.
    #[test]
    fn admit_bool_binary_function_mints_and_or_and_refuses_forgeries() {
        let u = Domain::Machine(MachineUIntWidth::U64);
        let i = Domain::Signed(MachineSIntWidth::I64);
        let mut env = Environment::with_prelude();
        // f(x) = 3 <= x && x <= 7  — a closed range guard.
        admit_bool_binary_function(
            &mut env,
            "range_def",
            &[u.clone()],
            BoolBinOp::And,
            SelectCmp::Le,
            CmpOperand::Const(3),
            CmpOperand::Param(0),
            SelectCmp::Le,
            CmpOperand::Param(0),
            CmpOperand::Const(7),
        )
        .expect("u64 range `&&` must admit");
        // g(x) = x <= 2 || 8 <= x  — a range exclusion.
        admit_bool_binary_function(
            &mut env,
            "excl_def",
            &[u.clone()],
            BoolBinOp::Or,
            SelectCmp::Le,
            CmpOperand::Param(0),
            CmpOperand::Const(2),
            SelectCmp::Le,
            CmpOperand::Const(8),
            CmpOperand::Param(0),
        )
        .expect("u64 exclusion `||` must admit");

        // NEG: mixed parameter domains fail closed.
        assert!(
            admit_bool_binary_function(
                &mut env,
                "mixed_bb",
                &[u.clone(), i.clone()],
                BoolBinOp::And,
                SelectCmp::Le,
                CmpOperand::Param(0),
                CmpOperand::Param(1),
                SelectCmp::Le,
                CmpOperand::Param(1),
                CmpOperand::Param(0),
            )
            .is_err(),
            "mixed-domain bool-binary stays outside the fragment"
        );
        // NEG: a constant-only leaf has no parameter fixing its carrier.
        assert!(
            admit_bool_binary_function(
                &mut env,
                "noparam_bb",
                &[u.clone()],
                BoolBinOp::And,
                SelectCmp::Le,
                CmpOperand::Param(0),
                CmpOperand::Const(7),
                SelectCmp::Le,
                CmpOperand::Const(1),
                CmpOperand::Const(2),
            )
            .is_err(),
            "a constant-only leaf has no carrier-fixing parameter"
        );
        // NEG: the `bool` domain is unordered, so a comparison leaf fails closed.
        assert!(
            admit_bool_binary_function(
                &mut env,
                "booldom_bb",
                &[Domain::Bool],
                BoolBinOp::And,
                SelectCmp::Le,
                CmpOperand::Param(0),
                CmpOperand::Param(0),
                SelectCmp::Le,
                CmpOperand::Param(0),
                CmpOperand::Param(0),
            )
            .is_err(),
            "bool comparison stays outside the fragment"
        );

        let tc = clean_kernel::TypeChecker::new(&env);
        let btrue = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let bfalse = Expr::const_(Name::from_string("Bool.false"), vec![]);
        let app1 = |f: &str, a: Expr| Expr::apps(Expr::const_(Name::from_string(f), vec![]), [a]);
        let un = |v: u64| u.numeral(u128::from(v)).unwrap();
        // range: 3 <= x <= 7.
        assert!(tc.is_def_eq(&app1("range_def", un(3)), &btrue), "3 ∈ [3,7]");
        assert!(tc.is_def_eq(&app1("range_def", un(5)), &btrue), "5 ∈ [3,7]");
        assert!(tc.is_def_eq(&app1("range_def", un(7)), &btrue), "7 ∈ [3,7]");
        assert!(tc.is_def_eq(&app1("range_def", un(2)), &bfalse), "2 ∉ [3,7] (below)");
        assert!(tc.is_def_eq(&app1("range_def", un(8)), &bfalse), "8 ∉ [3,7] (above)");
        // exclusion: x <= 2 || 8 <= x.
        assert!(tc.is_def_eq(&app1("excl_def", un(2)), &btrue), "2 excluded");
        assert!(tc.is_def_eq(&app1("excl_def", un(8)), &btrue), "8 excluded");
        assert!(tc.is_def_eq(&app1("excl_def", un(5)), &bfalse), "5 not excluded");
    }

    /// E6 widening increment 7, clause half — the SINGLE load-bearing property:
    /// a clause comparing an admitted `-> bool` bool-binary function against the
    /// `A && B` / `A || B` it computes elaborates to an `Eq Bool` whose two
    /// sides are DEFINITIONALLY EQUAL, so `ensures result == (A && B)` closes by
    /// `Eq.refl`. The mint's `Bool.and`/`Bool.or` of two decided leaves must be
    /// the VERY term [`elab_bool_term`] produces for the clause — not merely an
    /// equivalent one (the same iota lesson as the single comparison, one
    /// connective layer up).
    #[test]
    fn a_bool_binary_clause_is_defeq_to_the_bool_binary_mint() {
        for (rust_ty, dom) in [
            ("i64", Domain::Signed(MachineSIntWidth::I64)),
            ("u64", Domain::Machine(MachineUIntWidth::U64)),
        ] {
            let mut env = Environment::with_prelude();
            // AND: f(x) = 0 <= x && x <= 10.
            let adm_and = admit_bool_binary_function(
                &mut env,
                "rng_def",
                &[dom.clone()],
                BoolBinOp::And,
                SelectCmp::Le,
                CmpOperand::Const(0),
                CmpOperand::Param(0),
                SelectCmp::Le,
                CmpOperand::Param(0),
                CmpOperand::Const(10),
            )
            .expect("the `&&` mint must admit");
            assert_eq!(adm_and.return_domain().cloned(), Some(Domain::Bool), "records a Bool return domain");
            // OR: g(x) = x <= 0 || 10 <= x.
            let adm_or = admit_bool_binary_function(
                &mut env,
                "excl_def",
                &[dom.clone()],
                BoolBinOp::Or,
                SelectCmp::Le,
                CmpOperand::Param(0),
                CmpOperand::Const(0),
                SelectCmp::Le,
                CmpOperand::Const(10),
                CmpOperand::Param(0),
            )
            .expect("the `||` mint must admit");

            let t_and = admitted_table("rng", adm_and);
            let t_or = admitted_table("excl", adm_or);
            let vt: &[(&str, &str)] = &[("x", rust_ty)];
            let tc = clean_kernel::TypeChecker::new(&env);

            // `&&`: the clause term IS the mint term.
            let goal = elaborate_goal_typed_with_facets("rng(x) == (0 <= x && x <= 10)", vt, &t_and)
                .unwrap_or_else(|e| panic!("`&&` clause at {rust_ty} must elaborate: {e}"));
            let ty = tc
                .infer_type(&goal)
                .unwrap_or_else(|e| panic!("the {rust_ty} `&&` goal must be well-typed: {e:?}"));
            assert!(tc.is_def_eq(&ty, &Expr::sort(Level::zero())), "the goal must be a Prop");
            let (carrier, lhs, rhs) = eq_core(&goal);
            assert_eq!(
                carrier,
                Expr::const_(Name::from_string("Bool"), vec![]),
                "the relation carrier must be Bool at {rust_ty}"
            );
            assert!(
                tc.is_def_eq(&lhs, &rhs),
                "at {rust_ty} the mint and the `&&` clause must be def-eq — lhs={lhs:?} rhs={rhs:?}"
            );

            // Leaf ORDER matters: `B && A` is a structurally different neutral
            // term, so a positive test cannot pass by accidental commutation.
            let reordered =
                elaborate_goal_typed_with_facets("rng(x) == (x <= 10 && 0 <= x)", vt, &t_and)
                    .expect("the reordered `&&` clause must still elaborate");
            let (_, l2, r2) = eq_core(&reordered);
            assert!(!tc.is_def_eq(&l2, &r2), "`B && A` must NOT be the `A && B` mint");

            // `||`: the clause term IS the mint term.
            let goal_or =
                elaborate_goal_typed_with_facets("excl(x) == (x <= 0 || 10 <= x)", vt, &t_or)
                    .unwrap_or_else(|e| panic!("`||` clause at {rust_ty} must elaborate: {e}"));
            let (_, lo, ro) = eq_core(&goal_or);
            assert!(
                tc.is_def_eq(&lo, &ro),
                "at {rust_ty} the mint and the `||` clause must be def-eq — lhs={lo:?} rhs={ro:?}"
            );
        }
    }

    /// Checked-arithmetic admission, mint half: the mint admits exactly the
    /// recognizer's vocabulary and refuses everything else closed.
    #[test]
    fn admit_checked_arithmetic_function_mints_and_refuses_forgeries() {
        let i64d = Domain::Signed(MachineSIntWidth::I64);
        let i128d = Domain::Signed(MachineSIntWidth::I128);
        let mut env = Environment::with_prelude();
        for (name, op, width, dom) in [
            ("cadd64_def", CheckedArithOp::Add, MachineSIntWidth::I64, &i64d),
            ("csub64_def", CheckedArithOp::Sub, MachineSIntWidth::I64, &i64d),
            ("cmul64_def", CheckedArithOp::Mul, MachineSIntWidth::I64, &i64d),
            ("cadd128_def", CheckedArithOp::Add, MachineSIntWidth::I128, &i128d),
            ("cmul128_def", CheckedArithOp::Mul, MachineSIntWidth::I128, &i128d),
        ] {
            let adm = admit_checked_arithmetic_function(
                &mut env,
                name,
                &[dom.clone(), dom.clone()],
                op,
                width,
                CmpOperand::Param(0),
                CmpOperand::Param(1),
            )
            .unwrap_or_else(|e| panic!("{name} must admit: {e}"));
            assert_eq!(adm.arity, 2);
            assert_eq!(adm.return_domain().cloned(), Some(Domain::OptionSigned(width)));
            assert_eq!(adm.param_names, None, "parameters ARE the source parameters");
        }
        // A literal operand mints too (`x.checked_add(1)`), range-checked.
        admit_checked_arithmetic_function(
            &mut env,
            "cinc_def",
            &[i64d.clone()],
            CheckedArithOp::Add,
            MachineSIntWidth::I64,
            CmpOperand::Param(0),
            CmpOperand::Const(1),
        )
        .expect("a literal operand within iN must admit");

        // NEG: a parameter at the WRONG carrier (unsigned u64) fails closed.
        assert!(
            admit_checked_arithmetic_function(
                &mut env,
                "bad_unsigned",
                &[Domain::Machine(MachineUIntWidth::U64), Domain::Machine(MachineUIntWidth::U64)],
                CheckedArithOp::Add,
                MachineSIntWidth::I64,
                CmpOperand::Param(0),
                CmpOperand::Param(1),
            )
            .is_err(),
            "unsigned parameter domains must fail closed (spec §5.5)"
        );
        // NEG: mixed widths (i32 params under an i64 mint) fail closed.
        assert!(
            admit_checked_arithmetic_function(
                &mut env,
                "bad_width",
                &[Domain::Signed(MachineSIntWidth::I32), Domain::Signed(MachineSIntWidth::I32)],
                CheckedArithOp::Add,
                MachineSIntWidth::I64,
                CmpOperand::Param(0),
                CmpOperand::Param(1),
            )
            .is_err(),
            "width-mismatched parameters must fail closed"
        );
        // NEG: two literal operands leave no parameter fixing anything.
        assert!(
            admit_checked_arithmetic_function(
                &mut env,
                "bad_lits",
                &[i64d.clone()],
                CheckedArithOp::Add,
                MachineSIntWidth::I64,
                CmpOperand::Const(1),
                CmpOperand::Const(2),
            )
            .is_err(),
            "two-literal operands must fail closed"
        );
        // NEG: a negative literal has no recognizer spelling.
        assert!(
            admit_checked_arithmetic_function(
                &mut env,
                "bad_neg",
                &[i64d.clone()],
                CheckedArithOp::Add,
                MachineSIntWidth::I64,
                CmpOperand::Param(0),
                CmpOperand::NegConst(1),
            )
            .is_err(),
            "negative literal operands must fail closed"
        );
        // NEG: an out-of-range literal (2^63 does not fit i64's positives).
        assert!(
            admit_checked_arithmetic_function(
                &mut env,
                "bad_range",
                &[i64d.clone()],
                CheckedArithOp::Add,
                MachineSIntWidth::I64,
                CmpOperand::Param(0),
                CmpOperand::Const(1u128 << 63),
            )
            .is_err(),
            "an out-of-range literal must fail closed"
        );
        // NEG: an operand index past the arity.
        assert!(
            admit_checked_arithmetic_function(
                &mut env,
                "bad_index",
                &[i64d.clone()],
                CheckedArithOp::Add,
                MachineSIntWidth::I64,
                CmpOperand::Param(0),
                CmpOperand::Param(7),
            )
            .is_err(),
            "an out-of-range parameter index must fail closed"
        );

        // The SEEDED-HOMONYM guard: an env in which some island already
        // declared `trust_checked_checkedAdd64` with a DIFFERENT body must
        // refuse the mint outright rather than silently building on it.
        let mut poisoned = Environment::with_prelude();
        poisoned
            .add_decl(Declaration::Definition {
                name: Name::from_string("trust_checked_checkedAdd64"),
                level_params: vec![],
                type_: Expr::const_(Name::from_string("Bool"), vec![]),
                value: Expr::const_(Name::from_string("Bool.true"), vec![]),
                is_reducible: true,
            })
            .expect("poison decl registers");
        assert!(
            admit_checked_arithmetic_function(
                &mut poisoned,
                "cadd_on_poison",
                &[i64d.clone(), i64d.clone()],
                CheckedArithOp::Add,
                MachineSIntWidth::I64,
                CmpOperand::Param(0),
                CmpOperand::Param(1),
            )
            .is_err(),
            "a foreign homonym of a seeded model constant must refuse the mint"
        );
    }

    /// GUARDED-NARROW admission, mint half: the mint admits exactly the
    /// recognizer's (monomorphic) vocabulary, seeds both widths' checked
    /// models plus the two new definitions, and refuses everything else
    /// closed.
    #[test]
    fn admit_guarded_narrow_function_mints_and_refuses_forgeries() {
        let i128d = Domain::Signed(MachineSIntWidth::I128);
        let i64d = Domain::Signed(MachineSIntWidth::I64);
        let mut env = Environment::with_prelude();
        let adm = admit_guarded_narrow_function(
            &mut env,
            "narrow_def",
            std::slice::from_ref(&i128d),
            MachineSIntWidth::I128,
            MachineSIntWidth::I64,
            0,
        )
        .expect("the unary guarded-narrow shape must admit");
        assert_eq!(adm.arity, 1);
        assert_eq!(adm.return_domain().cloned(), Some(Domain::OptionSigned(MachineSIntWidth::I64)));
        assert_eq!(adm.param_names, None, "parameters ARE the source parameters");

        // The composed model is present: both widths' checked models plus the
        // two new definitions, all kernel-checked by `seed_decl`/`add_decl`.
        for seeded in [
            "trust_checked_toInt128",
            "trust_checked_fitsI64",
            "trust_checked_trunc128to64",
            "trust_checked_narrowI128toI64",
        ] {
            assert!(
                env.get_const(&Name::from_string(seeded)).is_some(),
                "`{seeded}` must be seeded by the guarded-narrow mint"
            );
        }
        // The minted equation IS the applied seeded constant, at the mixed
        // `BitVec 128 -> Option (BitVec 64)` type.
        let minted = env
            .get_const(&Name::from_string("narrow_def"))
            .expect("the mint registers")
            .clone();
        assert_eq!(
            minted.type_,
            Expr::arrow(i128d.ty(), Domain::OptionSigned(MachineSIntWidth::I64).ty()),
            "the minted type is BitVec 128 -> Option (BitVec 64)"
        );
        assert_eq!(
            minted.value,
            Some(Expr::lam(
                BinderInfo::Default,
                i128d.ty(),
                Expr::app(
                    Expr::const_(Name::from_string("trust_checked_narrowI128toI64"), vec![]),
                    Expr::bvar(0),
                ),
            )),
            "the minted body is the applied seeded model constant"
        );

        // Seeding is IDEMPOTENT: a sibling mint into the same env re-uses the
        // seeded definitions rather than colliding on them.
        admit_guarded_narrow_function(
            &mut env,
            "narrow_def_2",
            std::slice::from_ref(&i128d),
            MachineSIntWidth::I128,
            MachineSIntWidth::I64,
            0,
        )
        .expect("a sibling guarded-narrow mint must reuse the seeded model");

        // A MULTI-PARAMETER twin binds the narrowed parameter by INDEX, with
        // each parameter keeping its own carrier.
        let two = admit_guarded_narrow_function(
            &mut env,
            "narrow_def_p1",
            &[Domain::Bool, i128d.clone()],
            MachineSIntWidth::I128,
            MachineSIntWidth::I64,
            1,
        )
        .expect("a two-parameter twin must admit");
        assert_eq!(two.arity, 2);
        let two_value = env
            .get_const(&Name::from_string("narrow_def_p1"))
            .and_then(|c| c.value.clone())
            .expect("the two-parameter mint registers");
        assert_eq!(
            two_value,
            Expr::lam(
                BinderInfo::Default,
                Domain::Bool.ty(),
                Expr::lam(
                    BinderInfo::Default,
                    i128d.ty(),
                    Expr::app(
                        Expr::const_(Name::from_string("trust_checked_narrowI128toI64"), vec![]),
                        Expr::bvar(0),
                    ),
                ),
            ),
            "the outermost binder is p0 and the narrowed parameter is bvar(0) = p1"
        );

        // NEG: every non-(i128 -> Option<i64>) width pair PARKS.
        for (from, to) in [
            (MachineSIntWidth::I128, MachineSIntWidth::I32),
            (MachineSIntWidth::I128, MachineSIntWidth::I128),
            (MachineSIntWidth::I64, MachineSIntWidth::I64),
            (MachineSIntWidth::I32, MachineSIntWidth::I64),
        ] {
            assert!(
                admit_guarded_narrow_function(
                    &mut env,
                    "narrow_parked",
                    std::slice::from_ref(&i128d),
                    from,
                    to,
                    0,
                )
                .is_err(),
                "({from:?} -> Option<{to:?}>) must park"
            );
        }
        // NEG: the narrowed parameter off the source carrier, and an
        // out-of-range parameter index.
        assert!(
            admit_guarded_narrow_function(
                &mut env,
                "narrow_bad_carrier",
                std::slice::from_ref(&i64d),
                MachineSIntWidth::I128,
                MachineSIntWidth::I64,
                0,
            )
            .is_err(),
            "a narrowed parameter off the source carrier must fail closed"
        );
        assert!(
            admit_guarded_narrow_function(
                &mut env,
                "narrow_bad_index",
                std::slice::from_ref(&i128d),
                MachineSIntWidth::I128,
                MachineSIntWidth::I64,
                3,
            )
            .is_err(),
            "an out-of-range parameter index must fail closed"
        );
        assert!(
            admit_guarded_narrow_function(
                &mut env,
                "narrow_no_params",
                &[],
                MachineSIntWidth::I128,
                MachineSIntWidth::I64,
                0,
            )
            .is_err(),
            "a zero-parameter mint must fail closed"
        );

        // The SEEDED-HOMONYM guard reaches the two NEW definitions too.
        for homonym in ["trust_checked_trunc128to64", "trust_checked_narrowI128toI64"] {
            let mut poisoned = Environment::with_prelude();
            poisoned
                .add_decl(Declaration::Definition {
                    name: Name::from_string(homonym),
                    level_params: vec![],
                    type_: Expr::const_(Name::from_string("Bool"), vec![]),
                    value: Expr::const_(Name::from_string("Bool.true"), vec![]),
                    is_reducible: true,
                })
                .expect("poison decl registers");
            assert!(
                admit_guarded_narrow_function(
                    &mut poisoned,
                    "narrow_on_poison",
                    std::slice::from_ref(&i128d),
                    MachineSIntWidth::I128,
                    MachineSIntWidth::I64,
                    0,
                )
                .is_err(),
                "a foreign homonym of `{homonym}` must refuse the mint"
            );
        }
    }

    /// Checked-arithmetic admission, clause half: `ensures result ==
    /// Some(a + b)` / `result == None` elaborate to a WELL-TYPED
    /// `Eq (Option (BitVec N))` whose LHS is the admitted defining equation —
    /// and the constructor formers stay constructor-ONLY (spec §3.3/§3.4).
    #[test]
    fn a_checked_clause_elaborates_against_the_checked_mint() {
        let i64d = Domain::Signed(MachineSIntWidth::I64);
        let mut env = Environment::with_prelude();
        let adm = admit_checked_arithmetic_function(
            &mut env,
            "cadd_def",
            &[i64d.clone(), i64d.clone()],
            CheckedArithOp::Add,
            MachineSIntWidth::I64,
            CmpOperand::Param(0),
            CmpOperand::Param(1),
        )
        .expect("the checked mint must admit");
        let table = admitted_table("cadd", adm);
        let vt: &[(&str, &str)] = &[("a", "i64"), ("b", "i64")];
        let tc = clean_kernel::TypeChecker::new(&env);

        // `result == Some(a + b)` — after the self-rewrite, the goal is
        // `∀ a b, Eq (Option (BitVec 64)) (cadd_def a b) (some (a +ᵂ b))`.
        let goal = elaborate_ensures("result == Some(a + b)", vt, "cadd", &table)
            .expect("the Some clause must elaborate");
        let ty = tc.infer_type(&goal).expect("the Some goal must be well-typed");
        assert!(tc.is_def_eq(&ty, &Expr::sort(Level::zero())), "the goal must be a Prop");
        let (carrier, lhs, rhs) = eq_core(&goal);
        assert_eq!(
            carrier,
            Domain::OptionSigned(MachineSIntWidth::I64).ty(),
            "the relation carrier must be Option (BitVec 64)"
        );
        // The LHS is the minted constant applied to the two binders, which
        // unfolds to the seeded model applied the same way…
        let seeded = |name: &str| {
            Expr::apps(
                Expr::const_(Name::from_string(name), vec![]),
                [Expr::bvar(1), Expr::bvar(0)],
            )
        };
        assert!(
            tc.is_def_eq(&lhs, &seeded("trust_checked_checkedAdd64")),
            "the LHS must unfold to the seeded checkedAdd model"
        );
        // …and NOT to the sub/mul models (the add↔sub swap is caught).
        assert!(
            !tc.is_def_eq(&lhs, &seeded("trust_checked_checkedSub64")),
            "checkedAdd must not be def-eq to checkedSub"
        );
        assert!(
            !tc.is_def_eq(&lhs, &seeded("trust_checked_checkedMul64")),
            "checkedAdd must not be def-eq to checkedMul"
        );
        // The RHS is `Option.some (BitVec 64) (a +ᵂ b)` — the constructor over
        // the elaborator's own wrapping add.
        let expected_rhs = Expr::apps(
            Expr::const_(Name::from_string("Option.some"), vec![Level::zero()]),
            [
                i64d.ty(),
                i64d.arithmetic("add", Expr::bvar(1), Expr::bvar(0)).unwrap(),
            ],
        );
        assert_eq!(rhs, expected_rhs, "the Some side is the constructor over wrapping add");

        // `result == None` — the None constructor at the same carrier.
        let goal_none = elaborate_ensures("result == None", vt, "cadd", &table)
            .expect("the None clause must elaborate");
        tc.infer_type(&goal_none).expect("the None goal must be well-typed");
        let (_, _, rhs_none) = eq_core(&goal_none);
        assert_eq!(
            rhs_none,
            Expr::app(
                Expr::const_(Name::from_string("Option.none"), vec![Level::zero()]),
                i64d.ty()
            ),
            "the None side is the nullary constructor"
        );

        // `result != None` — desugars through Not(Eq …) and still types.
        let goal_ne = elaborate_ensures("result != None", vt, "cadd", &table)
            .expect("the != None clause must elaborate");
        tc.infer_type(&goal_ne).expect("the != None goal must be well-typed");

        // FAIL-CLOSED half. A constructor with no admitted-call side has no
        // carrier and is refused (no guessing).
        let err = elaborate_goal_typed_with_facets("Some(a) == Some(b)", vt, &table).unwrap_err();
        assert!(err.contains("Option"), "constructor-only equality must name the reason: {err}");
        // Option values are unordered.
        let err = elaborate_ensures("result <= None", vt, "cadd", &table).unwrap_err();
        assert!(err.contains("not ordered"), "{err}");
        // DESTRUCTORS stay outside the increment: `.unwrap()` fails closed.
        let err = elaborate_ensures("result.unwrap() == a", vt, "cadd", &table).unwrap_err();
        assert!(err.contains("method call"), "destructors must fail closed: {err}");
        // A bare variable cannot stand at the Option carrier.
        let err = elaborate_ensures("result == a", vt, "cadd", &table).unwrap_err();
        assert!(
            err.contains("Option"),
            "a scalar variable against an Option result must fail closed: {err}"
        );
    }

    /// The pre-existing `bool` clause shapes must elaborate to BYTE-IDENTICAL
    /// terms after the Bool-carrier lane landed: the new lane engages only for
    /// a decided form, never for a bare binding or a literal.
    #[test]
    fn bare_bool_equality_encoding_is_unchanged_by_the_decided_lane() {
        let dom = Domain::Bool;
        let flag = Expr::bvar(0);
        assert_eq!(
            elaborate_goal_typed("flag == true", &[("flag", "bool")]).unwrap(),
            Expr::pi(
                BinderInfo::Default,
                dom.ty(),
                dom.eq(flag.clone(), dom.bool_lit(true).unwrap())
            )
        );
        assert_eq!(
            elaborate_goal_typed("a == b", &[("a", "bool"), ("b", "bool")]).unwrap(),
            Expr::pi(
                BinderInfo::Default,
                dom.ty(),
                Expr::pi(BinderInfo::Default, dom.ty(), dom.eq(Expr::bvar(1), Expr::bvar(0)))
            )
        );
    }
}

#[cfg(test)]
mod certified_extended_carrier_tests {
    use clean_kernel::{Environment, TypeChecker};

    use super::*;

    fn kernel_checks_monitor(env: &Environment, monitor: &CertifiedMonitor) {
        TypeChecker::new(env)
            .check_type(monitor.equivalence_proof(), monitor.equivalence_goal())
            .expect("the Clean kernel must accept the monitor equivalence");
    }

    #[test]
    fn signed_comparison_monitors_are_kernel_checked_and_twos_complement_exact() {
        let env = Environment::with_prelude();
        for (ty, negative_one) in [
            ("i8", u8::MAX as u128),
            ("i16", u16::MAX as u128),
            ("i32", u32::MAX as u128),
            ("i64", u64::MAX as u128),
            ("i128", u128::MAX),
        ] {
            let monitor = certify_monitor_typed(&env, "x < y", &[("x", ty), ("y", ty)])
                .unwrap_or_else(|e| panic!("{ty} signed comparison must certify: {e}"));
            kernel_checks_monitor(&env, &monitor);
            let runtime = monitor.runtime();
            assert!(runtime.evaluate(&[("x", negative_one), ("y", 0)]).unwrap(), "{ty}: -1 < 0");
            assert!(!runtime.evaluate(&[("x", 0), ("y", negative_one)]).unwrap(), "{ty}: 0 !< -1");
        }
    }

    #[test]
    fn signed_and_u128_wrapping_arithmetic_certifies_at_boundaries() {
        let env = Environment::with_prelude();

        let i8_wrap = certify_monitor_typed(&env, "x + 1 == -128", &[("x", "i8")])
            .expect("i8 MAX+1=MIN monitor must certify");
        kernel_checks_monitor(&env, &i8_wrap);
        assert!(i8_wrap.runtime().evaluate(&[("x", i8::MAX as u128)]).unwrap());

        let i128_wrap = certify_monitor_typed(
            &env,
            "x + 1 == -170141183460469231731687303715884105728",
            &[("x", "i128")],
        )
        .expect("i128 MAX+1=MIN monitor must certify");
        kernel_checks_monitor(&env, &i128_wrap);
        assert!(i128_wrap.runtime().evaluate(&[("x", i128::MAX as u128)]).unwrap());

        let u128_wrap = certify_monitor_typed(&env, "x + 1 == 0", &[("x", "u128")])
            .expect("u128 wrapping monitor must certify");
        kernel_checks_monitor(&env, &u128_wrap);
        assert!(u128_wrap.runtime().evaluate(&[("x", u128::MAX)]).unwrap());

        let u128_literal = certify_monitor_typed(
            &env,
            "x == 340282366920938463463374607431768211455",
            &[("x", "u128")],
        )
        .expect("u128::MAX literal must stay lossless");
        assert!(u128_literal.runtime().evaluate(&[("x", u128::MAX)]).unwrap());
    }

    #[test]
    fn pointer_carriers_require_and_honor_an_explicit_target_width() {
        let env = Environment::with_prelude();

        assert!(
            certify_monitor_typed(&env, "x == x", &[("x", "usize")]).is_err(),
            "bare usize must never guess the target"
        );
        let u16_target = certify_monitor_typed_for_target(
            &env,
            "x + 1 == 0",
            &[("x", "usize")],
            TargetPointerWidth::W16,
        )
        .expect("16-bit usize monitor must certify");
        kernel_checks_monitor(&env, &u16_target);
        assert!(u16_target.runtime().evaluate(&[("x", u16::MAX as u128)]).unwrap());
        assert_eq!(u16_target.runtime().domain("x"), Some(RuntimeMonitorDomain::USize16));

        let i16_target = certify_monitor_typed_for_target(
            &env,
            "x < 0",
            &[("x", "isize")],
            TargetPointerWidth::W16,
        )
        .expect("16-bit isize monitor must certify");
        kernel_checks_monitor(&env, &i16_target);
        assert!(i16_target.runtime().evaluate(&[("x", u16::MAX as u128)]).unwrap());
        assert_eq!(i16_target.runtime().domain("x"), Some(RuntimeMonitorDomain::ISize16));

        let u32_target = certify_monitor_typed_for_target(
            &env,
            "x + 1 == 0",
            &[("x", "usize")],
            TargetPointerWidth::W32,
        )
        .expect("32-bit usize monitor must certify");
        kernel_checks_monitor(&env, &u32_target);
        assert!(u32_target.runtime().evaluate(&[("x", u32::MAX as u128)]).unwrap());
        assert_eq!(u32_target.runtime().domain("x"), Some(RuntimeMonitorDomain::USize32));

        let i64_target = certify_monitor_typed_for_target(
            &env,
            "x < 0",
            &[("x", "isize")],
            TargetPointerWidth::W64,
        )
        .expect("64-bit isize monitor must certify");
        kernel_checks_monitor(&env, &i64_target);
        assert!(i64_target.runtime().evaluate(&[("x", u64::MAX as u128)]).unwrap());
        assert_eq!(i64_target.runtime().domain("x"), Some(RuntimeMonitorDomain::ISize64));

        assert!(
            certify_monitor_typed_for_target(
                &env,
                "x == x",
                &[("x", "usize32")],
                TargetPointerWidth::W64,
            )
            .is_err(),
            "a pre-resolved pointer spelling that conflicts with the target must fail closed"
        );
    }

    /// E9 discharge binders: bare `usize`/`isize` resolve to the fixed-width
    /// machine spelling of the TARGET's width — the carrier the E6 import of a
    /// `usize` function is minted at — and to nothing else.
    #[test]
    fn discharge_binders_resolve_pointer_sized_names_at_the_target_width_only() {
        for (width, unsigned, signed) in [
            (TargetPointerWidth::W16, "u16", "i16"),
            (TargetPointerWidth::W32, "u32", "i32"),
            (TargetPointerWidth::W64, "u64", "i64"),
        ] {
            assert_eq!(discharge_binding_ty_for_target("usize", width), unsigned);
            assert_eq!(discharge_binding_ty_for_target("isize", width), signed);
            // Every other name is the identity: a fixed-width type is never
            // re-read through the pointer width, an already-explicit pointer
            // spelling is never rewritten, and an unsupported name stays
            // unsupported.
            for name in ["u8", "u64", "i64", "u128", "bool", "nat", "usize64", "isize32", "Vec"] {
                assert_eq!(discharge_binding_ty_for_target(name, width), name);
            }
        }

        // POSITIVE: the resolved goal IS the fixed-width goal, byte for byte,
        // so everything proved about a `u64` clause applies to a `usize`
        // clause on a 64-bit target and nothing new is admitted.
        let resolved = discharge_binding_ty_for_target("usize", TargetPointerWidth::W64);
        let usize_goal = elaborate_goal_typed("n <= n", &[("n", resolved)])
            .expect("a 64-bit usize clause elaborates");
        let u64_goal =
            elaborate_goal_typed("n <= n", &[("n", "u64")]).expect("the u64 clause elaborates");
        assert_eq!(usize_goal, u64_goal);

        // WIDTH NEGATIVE CONTROL: the same clause on a 32-bit target is a
        // DIFFERENT proposition (it quantifies over `UInt32`), so a proof of
        // the 64-bit statement cannot inhabit it.
        let resolved32 = discharge_binding_ty_for_target("usize", TargetPointerWidth::W32);
        let usize32_goal = elaborate_goal_typed("n <= n", &[("n", resolved32)])
            .expect("a 32-bit usize clause elaborates");
        assert_ne!(usize32_goal, u64_goal, "a 32-bit usize clause must not be the 64-bit goal");

        // CLOSE NEGATIVE TWIN: the UNRESOLVED name is still refused — the
        // resolution, not a relaxed binding gate, is what admits the clause.
        let refused = elaborate_goal_typed("n <= n", &[("n", "usize")])
            .expect_err("bare usize must never guess the target");
        assert!(refused.contains("unsupported clause variable type `usize`"), "{refused}");
    }

    #[test]
    fn scalar_measure_is_sealed_kernel_checked_and_runtime_exact() {
        let env = Environment::with_prelude();
        let measure = certify_measure_typed(&env, "x - 1", &[("x", "u128")])
            .expect("u128 measure must certify");
        TypeChecker::new(&env)
            .check_type(measure.binding_proof(), measure.binding_goal())
            .expect("kernel accepts the scalar binding theorem");
        assert_eq!(measure.runtime().domain(), RuntimeMonitorDomain::U128);
        assert_eq!(measure.runtime().evaluate(&[("x", 0)]).unwrap(), u128::MAX);

        let pointer_measure = certify_measure_typed_for_target(
            &env,
            "x + 1",
            &[("x", "usize")],
            TargetPointerWidth::W32,
        )
        .expect("target-resolved usize measure must certify");
        assert_eq!(pointer_measure.runtime().domain(), RuntimeMonitorDomain::USize32);
        assert_eq!(pointer_measure.runtime().evaluate(&[("x", u32::MAX as u128)]).unwrap(), 0);
    }

    #[test]
    fn extended_carriers_fail_closed_on_unimplemented_or_ill_typed_operations() {
        let env = Environment::with_prelude();
        assert!(certify_monitor_typed(&env, "x / 2 == 0", &[("x", "i8")]).is_err());
        assert!(certify_monitor_typed(&env, "x % 2 == 0", &[("x", "i64")]).is_err());
        assert!(certify_monitor_typed(&env, "x >> 1 == x", &[("x", "i128")]).is_err());
        assert!(certify_monitor_typed(&env, "x + 128 == x", &[("x", "i8")]).is_err());
        assert!(certify_monitor_typed(&env, "x == -1", &[("x", "u128")]).is_err());
        assert!(certify_monitor_typed(&env, "x == -129", &[("x", "i8")]).is_err());

        let i8_monitor =
            certify_monitor_typed(&env, "x == x", &[("x", "i8")]).expect("i8 equality certifies");
        assert!(
            i8_monitor.runtime().evaluate(&[("x", 256)]).is_err(),
            "out-of-carrier bit patterns are rejected"
        );
    }
}

/// The nat-lift fragment (design `scratchpad/designs/design-nat-lift.v2.md`):
/// the explicit `e as nat` / `e as int` lift, its closed table, the
/// self-determination rule, and the refusals.
///
/// Every positive here is checked against the KERNEL — the goal must be a
/// well-typed proposition, and where the design claims definitional equality
/// the `Eq.refl` term must actually close it and GRADE `Certified`. Every
/// positive has a close negative twin, and the two soundness-critical rules
/// (self-determination, and the two-read cross-check on the self function)
/// carry mutation controls that show the twin has teeth.
#[cfg(test)]
mod nat_lift_tests {
    use super::*;
    use clean_kernel::expr::BinderInfo;
    use clean_kernel::{Declaration, TypeChecker};

    fn cert() -> FacetStatus {
        FacetStatus::Certified { evidence: "nat-lift test".into() }
    }

    fn admissible() -> FnFacets {
        FnFacets { pure: cert(), total: cert(), deterministic: cert(), no_panic: cert() }
    }

    fn c(n: &str) -> Expr {
        Expr::const_(Name::from_string(n), vec![])
    }

    fn u64d() -> Domain {
        Domain::Machine(MachineUIntWidth::U64)
    }

    fn u32d() -> Domain {
        Domain::Machine(MachineUIntWidth::U32)
    }

    fn i64d() -> Domain {
        Domain::Signed(MachineSIntWidth::I64)
    }

    /// Declare an ISLAND-STYLE definition: a plain kernel `Definition` over the
    /// given domains, admitted with its declared carriers recorded. This is the
    /// same shape `admit_certified_island_definition` produces for a
    /// `clean { def … }` body — a Lean definition over `Nat`/`Int`, which is
    /// what every owner model is written in.
    fn declare_island_def(
        env: &mut Environment,
        facets: &mut FacetTable,
        clause_name: &str,
        kernel_const: &str,
        params: &[Domain],
        ret: &Domain,
        body: Expr,
    ) {
        let ty = params.iter().rev().fold(ret.ty(), |acc, d| Expr::arrow(d.ty(), acc));
        let value = params.iter().rev().fold(body, |acc, d| Expr::lam(BinderInfo::Default, d.ty(), acc));
        env.add_decl(Declaration::Definition {
            name: Name::from_string(kernel_const),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
        .expect("the island-style definition must be well-typed");
        facets.insert(clause_name, admissible());
        facets.admit(
            clause_name,
            Admission::reflected(kernel_const, params.len()).with_declared_signature(
                Some(ret.clone()),
                Some(DeclaredCarriers::of_domains(params, ret)),
            ),
        );
    }

    /// The ensures-discharge goal for a PROOF-position clause with lifts, and
    /// the widths whose seeded lift model it names.
    fn lifted(
        clause: &str,
        params: &[(&str, &str)],
        self_fn: &str,
        result_ty: &str,
        facets: &FacetTable,
    ) -> Result<ElaboratedClause, String> {
        elaborate_ensures_in(
            clause,
            params,
            self_fn,
            facets,
            &ProofClauseInputs::proof_lift(Some(result_ty)),
        )
    }

    // ---------------------------------------------------------------- WE-1

    /// WE-1: a `u64` function proved against a `Nat`-carrier Lean definition,
    /// by definitional equality. THE flagship: before this, the clause could
    /// not even be stated ("declares parameter 0 at carrier `Nat`, but the
    /// argument is a `u64` term ... never coerced").
    #[test]
    fn we1_u64_function_discharges_against_a_nat_definition_by_defeq() {
        let mut env = Environment::with_prelude();
        let mut facets = FacetTable::new();
        // clean { def first_nat (a : Nat) (b : Nat) : Nat := a }
        declare_island_def(
            &mut env,
            &mut facets,
            "first_nat",
            "first_nat_def",
            &[Domain::Nat, Domain::Nat],
            &Domain::Nat,
            Expr::bvar(1),
        );
        // pub fn first(a: u64, b: u64) -> u64 { a }
        let first = admit_projection_function(&mut env, "first_def", &[u64d(), u64d()], 0)
            .expect("the Rust projection admits");
        facets.insert("first", admissible());
        facets.admit("first", first.with_declared_signature(Some(u64d()), None));

        let clause = lifted(
            "(result as nat) == first_nat(a as nat, b as nat)",
            &[("a", "u64"), ("b", "u64")],
            "first",
            "u64",
            &facets,
        )
        .expect("the lifted clause must elaborate");
        assert!(clause.required_signed_lift_widths.is_empty(), "an unsigned lift seeds nothing");

        // The goal is EXACTLY the design's WE-1 shape.
        let to_nat = |e: Expr| Expr::app(c("UInt64.toNat"), e);
        let bind = |body: Expr| {
            Expr::pi(
                BinderInfo::Default,
                c("UInt64"),
                Expr::pi(BinderInfo::Default, c("UInt64"), body),
            )
        };
        let lhs = to_nat(Expr::apps(c("first_def"), [Expr::bvar(1), Expr::bvar(0)]));
        let rhs = Expr::apps(c("first_nat_def"), [to_nat(Expr::bvar(1)), to_nat(Expr::bvar(0))]);
        assert_eq!(clause.goal, bind(Domain::Nat.eq(lhs.clone(), rhs)), "WE-1 goal shape");

        // KERNEL: well-typed, and `Eq.refl` closes it with an empty closure.
        let tc = TypeChecker::new(&env);
        let _ = tc.infer_sort(&clause.goal).expect("the lifted goal must be well-typed");
        let proof = Expr::lam(
            BinderInfo::Default,
            c("UInt64"),
            Expr::lam(
                BinderInfo::Default,
                c("UInt64"),
                Expr::apps(
                    Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]),
                    [c("Nat"), lhs],
                ),
            ),
        );
        assert_eq!(
            cert_meter::grade(&env, &clause.goal, &proof),
            cert_meter::Grade::Certified,
            "WE-1 must discharge by defeq and GRADE Certified"
        );
    }

    /// WE-1 NEG-a: the same clause against the WRONG projection. The lift is
    /// exact, so the two sides are genuinely different terms and `Eq.refl` must
    /// not close them. (`first` returns `a`; the clause claims `b`.)
    #[test]
    fn we1_neg_wrong_projection_is_not_definitional() {
        let mut env = Environment::with_prelude();
        let mut facets = FacetTable::new();
        declare_island_def(
            &mut env,
            &mut facets,
            "second_nat",
            "second_nat_def",
            &[Domain::Nat, Domain::Nat],
            &Domain::Nat,
            Expr::bvar(0),
        );
        let first = admit_projection_function(&mut env, "first_def", &[u64d(), u64d()], 0)
            .expect("the Rust projection admits");
        facets.insert("first", admissible());
        facets.admit("first", first.with_declared_signature(Some(u64d()), None));

        let clause = lifted(
            "(result as nat) == second_nat(a as nat, b as nat)",
            &[("a", "u64"), ("b", "u64")],
            "first",
            "u64",
            &facets,
        )
        .expect("the clause still elaborates — it is simply false");
        let tc = TypeChecker::new(&env);
        let _ = tc.infer_sort(&clause.goal).expect("still a well-typed proposition");
        let to_nat = |e: Expr| Expr::app(c("UInt64.toNat"), e);
        let lhs = to_nat(Expr::apps(c("first_def"), [Expr::bvar(1), Expr::bvar(0)]));
        let proof = Expr::lam(
            BinderInfo::Default,
            c("UInt64"),
            Expr::lam(
                BinderInfo::Default,
                c("UInt64"),
                Expr::apps(
                    Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]),
                    [c("Nat"), lhs],
                ),
            ),
        );
        assert!(
            tc.check_type(&proof, &clause.goal).is_err(),
            "the wrong projection must NOT be definitionally equal"
        );
    }

    /// WE-1 NEG-b, the WRAP twin, and mutation control m1. A wrapping Rust body
    /// does NOT satisfy the `Nat`-level successor equation. This is the fact
    /// that makes rejected option F (narrowing the Lean side with `ofNat`)
    /// unsound: under it this goal would be TRUE.
    #[test]
    fn we1_neg_wrapping_body_does_not_satisfy_the_nat_equation() {
        let mut env = Environment::with_prelude();
        let mut facets = FacetTable::new();
        // clean { def succ_nat (n : Nat) : Nat := n + 1 }
        declare_island_def(
            &mut env,
            &mut facets,
            "succ_nat",
            "succ_nat_def",
            &[Domain::Nat],
            &Domain::Nat,
            Expr::apps(c("Nat.add"), [Expr::bvar(0), Expr::nat_lit(1)]),
        );
        // pub fn succ(x: u64) -> u64 { x.wrapping_add(1) }
        env.add_decl(Declaration::Definition {
            name: Name::from_string("succ_def"),
            level_params: vec![],
            type_: Expr::arrow(c("UInt64"), c("UInt64")),
            value: Expr::lam(
                BinderInfo::Default,
                c("UInt64"),
                Expr::apps(
                    c("UInt64.add"),
                    [Expr::bvar(0), Expr::app(c("UInt64.ofNat"), Expr::nat_lit(1))],
                ),
            ),
            is_reducible: true,
        })
        .expect("the wrapping body is well-typed");
        facets.insert("succ", admissible());
        facets.admit(
            "succ",
            Admission::reflected("succ_def", 1).with_declared_signature(Some(u64d()), None),
        );

        let clause =
            lifted("(result as nat) == succ_nat(x as nat)", &[("x", "u64")], "succ", "u64", &facets)
                .expect("the clause elaborates");
        let tc = TypeChecker::new(&env);
        let _ = tc.infer_sort(&clause.goal).expect("well-typed");
        let lhs =
            Expr::app(c("UInt64.toNat"), Expr::app(c("succ_def"), Expr::bvar(0)));
        let proof = Expr::lam(
            BinderInfo::Default,
            c("UInt64"),
            Expr::apps(
                Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]),
                [c("Nat"), lhs],
            ),
        );
        assert!(
            tc.check_type(&proof, &clause.goal).is_err(),
            "a wrapping body must NOT satisfy the unbounded successor equation"
        );
    }

    // ------------------------------------------------- the (Math, Math) row

    /// F-2, the relation carrier. The atom's operands are `Nat` terms, so the
    /// relation must be built at `Nat` — NOT at the `u32` the clause variables
    /// would suggest. The pre-existing `atom_domain` resolves over every free
    /// variable INCLUDING a typed call's arguments, so without §3.4 this builds
    /// `Nat.le (UInt32.toNat (clamp_nat …)) …`, which does not type.
    #[test]
    fn math_math_order_row_is_built_at_nat_not_at_the_variables_width() {
        let mut env = Environment::with_prelude();
        let mut facets = FacetTable::new();
        // clean { def min_nat (c : Nat) (d : Nat) : Nat := Nat.min c d }
        declare_island_def(
            &mut env,
            &mut facets,
            "min_nat",
            "min_nat_def",
            &[Domain::Nat, Domain::Nat],
            &Domain::Nat,
            Expr::apps(c("Nat.min"), [Expr::bvar(1), Expr::bvar(0)]),
        );
        let clamp = admit_projection_function(&mut env, "clamp_def", &[u32d(), u32d()], 0)
            .expect("mints");
        facets.insert("clamp", admissible());
        facets.admit("clamp", clamp.with_declared_signature(Some(u32d()), None));

        let clause = lifted(
            "min_nat(c as nat, d as nat) <= (d as nat)",
            &[("c", "u32"), ("d", "u32")],
            "clamp",
            "u32",
            &facets,
        )
        .expect("the (Math, Math) order row must elaborate");

        let to_nat = |e: Expr| Expr::app(c("UInt32.toNat"), e);
        let expected = Expr::pi(
            BinderInfo::Default,
            c("UInt32"),
            Expr::pi(
                BinderInfo::Default,
                c("UInt32"),
                Domain::Nat.cmp(
                    "le",
                    Expr::apps(c("min_nat_def"), [to_nat(Expr::bvar(1)), to_nat(Expr::bvar(0))]),
                    to_nat(Expr::bvar(0)),
                ),
            ),
        );
        assert_eq!(clause.goal, expected, "the relation must be `Nat.le`, at `Nat`");
        let _ = TypeChecker::new(&env)
            .infer_sort(&clause.goal)
            .expect("the Nat-level order goal must be well-typed");
    }

    /// Mutation control m-F2: the shape the PRE-EXISTING path would have built
    /// for that atom — the relation at the variables' machine width — is
    /// ill-typed. So §3.4 is load-bearing, not cosmetic.
    #[test]
    fn mutation_the_machine_carrier_relation_over_a_nat_term_does_not_type() {
        let mut env = Environment::with_prelude();
        env.add_decl(Declaration::Definition {
            name: Name::from_string("min_nat_def"),
            level_params: vec![],
            type_: Expr::arrow(c("Nat"), Expr::arrow(c("Nat"), c("Nat"))),
            value: Expr::lam(
                BinderInfo::Default,
                c("Nat"),
                Expr::lam(
                    BinderInfo::Default,
                    c("Nat"),
                    Expr::apps(c("Nat.min"), [Expr::bvar(1), Expr::bvar(0)]),
                ),
            ),
            is_reducible: true,
        })
        .expect("well-typed");
        // `Nat.le (UInt32.toNat (min_nat_def …)) (UInt32.toNat d)` — `toNat`
        // applied to a `Nat`.
        let bad = Expr::pi(
            BinderInfo::Default,
            c("UInt32"),
            u32d().cmp(
                "le",
                Expr::apps(c("min_nat_def"), [Expr::nat_lit(1), Expr::nat_lit(2)]),
                Expr::bvar(0),
            ),
        );
        assert!(
            TypeChecker::new(&env).infer_sort(&bad).is_err(),
            "the machine-carrier relation over a Nat term must NOT type — this is what \\
             §3.4 exists to prevent"
        );
    }

    // ---------------------------------------------------------------- WE-3

    /// WE-3: an `i64` function against an `Int`-carrier definition, through the
    /// EXISTING seeded two's-complement value model. The elaborator names the
    /// constant; the caller must seed it, and the clause says which widths.
    #[test]
    fn we3_i64_function_discharges_against_an_int_definition() {
        let mut env = Environment::with_prelude();
        seed_signed_lift_model(&mut env, MachineSIntWidth::I64).expect("seeds");
        let mut facets = FacetTable::new();
        // clean { def ident_i (x : Int) : Int := x }
        declare_island_def(
            &mut env,
            &mut facets,
            "ident_i",
            "ident_i_def",
            &[Domain::Int],
            &Domain::Int,
            Expr::bvar(0),
        );
        let idi = admit_projection_function(&mut env, "idi_def", &[i64d()], 0).expect("mints");
        facets.insert("idi", admissible());
        facets.admit("idi", idi.with_declared_signature(Some(i64d()), None));

        let clause =
            lifted("(result as int) == ident_i(x as int)", &[("x", "i64")], "idi", "i64", &facets)
                .expect("the signed lift must elaborate");
        assert_eq!(
            clause.required_signed_lift_widths,
            vec![MachineSIntWidth::I64],
            "the clause must DECLARE the seeding obligation it created"
        );

        let to_int = |e: Expr| Expr::app(c(&signed_lift_const_name(MachineSIntWidth::I64)), e);
        let bv64 = Expr::app(c("BitVec"), Expr::nat_lit(64));
        let lhs = to_int(Expr::app(c("idi_def"), Expr::bvar(0)));
        let expected = Expr::pi(
            BinderInfo::Default,
            bv64.clone(),
            Domain::Int.eq(lhs.clone(), Expr::app(c("ident_i_def"), to_int(Expr::bvar(0)))),
        );
        assert_eq!(clause.goal, expected, "WE-3 goal shape");

        let tc = TypeChecker::new(&env);
        let _ = tc.infer_sort(&clause.goal).expect("the signed lifted goal must be well-typed");
        let proof = Expr::lam(
            BinderInfo::Default,
            bv64,
            Expr::apps(
                Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]),
                [c("Int"), lhs],
            ),
        );
        assert_eq!(
            cert_meter::grade(&env, &clause.goal, &proof),
            cert_meter::Grade::Certified,
            "WE-3 must discharge by defeq and GRADE Certified"
        );
    }

    // ------------------------------------------- self-determination (S-1)

    /// Build the S-1 table: `bv_id : BitVec 128 -> BitVec 128` (a signedness
    /// TRANSMUTE, whose recorded return domain is therefore withheld) and
    /// `nat_fst`/`int_id` over the math carriers.
    fn s1_facets(env: &mut Environment) -> FacetTable {
        let mut facets = FacetTable::new();
        let bv128 = Expr::app(c("BitVec"), Expr::nat_lit(128));
        env.add_decl(Declaration::Definition {
            name: Name::from_string("bv_id_def"),
            level_params: vec![],
            type_: Expr::arrow(bv128.clone(), bv128.clone()),
            value: Expr::lam(BinderInfo::Default, bv128, Expr::bvar(0)),
            is_reducible: true,
        })
        .expect("well-typed");
        facets.insert("bv_id", admissible());
        // DECLARED CARRIERS but NO return domain — exactly what the island
        // admitter produces for `def bv_id (v : BitVec 128) : BitVec 128`:
        // `BitVec 128` has three Rust preimages (`i128`, `u128`, and a
        // 128-bit pointer-sized int), so `island_return_domain` deliberately
        // answers `None` while the carriers are still read back.
        facets.admit(
            "bv_id",
            Admission::reflected("bv_id_def", 1).with_declared_signature(
                None,
                Some(DeclaredCarriers::of_domains(&[Domain::U128], &Domain::U128)),
            ),
        );
        declare_island_def(
            env,
            &mut facets,
            "nat_fst",
            "nat_fst_def",
            &[Domain::Nat, Domain::Nat],
            &Domain::Nat,
            Expr::bvar(1),
        );
        declare_island_def(
            env,
            &mut facets,
            "int_id",
            "int_id_def",
            &[Domain::Int],
            &Domain::Int,
            Expr::bvar(0),
        );
        facets
    }

    /// S-1a (BLOCKING in the design review): a lift is NEVER decided from a
    /// sibling argument. `bv_id(a)` with `a : i128` beside `s : u128` would,
    /// under the pre-existing `argument_domain` fallback, take `u128` from its
    /// SIBLING and read the same bit pattern as `2^128 - 1` where the author
    /// wrote `-1`. Both goals are well-typed, so the kernel cannot catch it.
    #[test]
    fn s1a_a_sibling_never_decides_a_lift() {
        let mut env = Environment::with_prelude();
        let mut facets = s1_facets(&mut env);
        let f = admit_projection_function(&mut env, "f_def", &[u64d()], 0).expect("mints");
        facets.insert("f", admissible());
        facets.admit("f", f.with_declared_signature(Some(u64d()), None));

        let err = lifted(
            "nat_fst(bv_id(a) as nat, s as nat) == (r as nat)",
            &[("a", "i128"), ("s", "u128"), ("r", "u64")],
            "f",
            "u64",
            &facets,
        )
        .expect_err("a non-self-determined lift must be refused");
        assert!(
            err.contains("not determined") || err.contains("no recorded result domain"),
            "the refusal must name self-determination, got: {err}"
        );
        // NOT `err.contains("BitVec 128")` on its own: `unpinned_lift_error`
        // puts "`i128` and `u128` share the carrier `BitVec 128`" into EVERY
        // unpinned message whatever the cause, so that assertion carried no
        // information (found in integration review, 2026-09-17). Pin the part
        // that is about THIS term: the callee it could not pin, and the
        // carrier-ambiguity reason in the head sentence rather than the note.
        assert!(err.contains("bv_id"), "and name the term it refused: {err}");
        assert!(
            err.contains("more than one Rust preimage")
                || err.contains("no recorded result domain"),
            "and the REASON is about `bv_id`'s codomain, not the boilerplate note: {err}"
        );
    }

    /// Mutation control m4, stated as a MEASUREMENT: the pre-existing sibling
    /// fallback really would have answered `u128` for `bv_id(a)`, so S-1a's
    /// refusal is the strict rule doing work rather than an accident of some
    /// other check. If `pinned_domain` were relaxed to use `argument_domain`,
    /// S-1a would go green with the wrong signedness.
    #[test]
    fn mutation_m4_the_sibling_fallback_would_have_answered_u128() {
        let mut env = Environment::with_prelude();
        let facets = s1_facets(&mut env);
        let _scope = AdmissionScope::enter_at(facets, trust_symbols::Capability::Proof);
        let call: SynExpr =
            syn::parse_str("nat_fst(bv_id(a), s)").expect("parses");
        let SynExpr::Call(call) = &call else { panic!("a call") };
        let arg = &call.args[0];
        let var_domains: BTreeMap<String, Domain> = [
            ("a".to_string(), Domain::Signed(MachineSIntWidth::I128)),
            ("s".to_string(), Domain::U128),
        ]
        .into_iter()
        .collect();

        // The pre-existing rule: the SIBLING decides.
        let borrowed = argument_domain(arg, call, &var_domains, &Domain::Nat)
            .expect("the pre-existing rule answers");
        assert_eq!(
            borrowed,
            Domain::U128,
            "the sibling fallback borrows `u128` — the exact borrow that would make the \\
             signed value read as 2^128 - 1"
        );
        // The self-determination rule: it does not.
        assert!(
            matches!(
                pinned_domain(arg, &var_domains).expect("classifies"),
                TermPin::Unpinned(_)
            ),
            "the self-determination rule must refuse to decide"
        );
    }

    /// S-1c: the same transmute inside ARITHMETIC. `bv_id(a) + b` is typed
    /// `u128` by rule 1 from `b` alone under the pre-existing path; the
    /// self-determination rule still refuses, because an unpinned operand
    /// poisons the whole term.
    #[test]
    fn s1c_a_transmute_inside_arithmetic_is_still_unpinned() {
        let mut env = Environment::with_prelude();
        let mut facets = s1_facets(&mut env);
        let f = admit_projection_function(&mut env, "f_def", &[u64d()], 0).expect("mints");
        facets.insert("f", admissible());
        facets.admit("f", f.with_declared_signature(Some(u64d()), None));

        let err = lifted(
            "int_id((bv_id(a) + b) as int) == (r as int)",
            &[("a", "i128"), ("b", "u128"), ("r", "u64")],
            "f",
            "u64",
            &facets,
        )
        .expect_err("an unpinned operand must poison the lift");
        assert!(
            err.contains("not determined") || err.contains("no recorded result domain"),
            "got: {err}"
        );
    }

    // ------------------------------------------- the two-read cross-check

    fn self_crosscheck_facets(env: &mut Environment) -> FacetTable {
        let mut facets = FacetTable::new();
        declare_island_def(
            env,
            &mut facets,
            "big_int",
            "big_int_def",
            &[Domain::Int],
            &Domain::Int,
            Expr::bvar(0),
        );
        let big = admit_projection_function(env, "big_def", &[Domain::U128], 0).expect("mints");
        facets.insert("big", admissible());
        facets.admit("big", big.with_declared_signature(Some(Domain::U128), None));
        facets
    }

    /// F-3: the SELF function's recorded return domain is cross-checked against
    /// the compiler's own resolved return type. `u128` and `i128` share the
    /// carrier `BitVec 128`, so a wrongly recorded domain yields a WELL-TYPED
    /// goal about the wrong integer — the kernel cannot catch it, which is why
    /// this is checked twice. Agreement: accepted.
    #[test]
    fn f3_self_return_domain_agreeing_with_typeck_is_accepted() {
        let mut env = Environment::with_prelude();
        let facets = self_crosscheck_facets(&mut env);
        let clause =
            lifted("(result as int) == big_int(a as int)", &[("a", "u128")], "big", "u128", &facets)
                .expect("the two reads agree, so the lift is allowed");
        let _ = TypeChecker::new(&env).infer_sort(&clause.goal).expect("well-typed");
        assert!(
            clause.required_signed_lift_widths.is_empty(),
            "the unsigned `u128 -> Int` row seeds nothing"
        );
    }

    /// F-3 mutation control m6: record `i128` on a `u128` function. The two
    /// reads disagree and the lift is refused — it is the cross-check that
    /// holds this, not the kernel, because both readings type.
    #[test]
    fn mutation_m6_a_wrongly_recorded_self_return_domain_is_refused() {
        let mut env = Environment::with_prelude();
        let mut facets = self_crosscheck_facets(&mut env);
        // The mutation: the mint records the WRONG signedness at the shared
        // carrier.
        facets.admit(
            "big",
            Admission::reflected("big_def", 1)
                .with_declared_signature(Some(Domain::Signed(MachineSIntWidth::I128)), None),
        );
        let err = lifted(
            "(result as int) == big_int(a as int)",
            &[("a", "u128")],
            "big",
            "u128",
            &facets,
        )
        .expect_err("the two reads disagree, so the lift must fail closed");
        assert!(err.contains("two reads"), "the refusal must name the disagreement: {err}");
        assert!(err.contains("u128") && err.contains("i128"), "and both readings: {err}");
    }

    /// D-10's other half: with NO second read the lift of a `result`-headed
    /// term fails CLOSED rather than trusting the single recorded domain.
    #[test]
    fn d10_no_second_read_refuses_the_self_lift() {
        let mut env = Environment::with_prelude();
        let facets = self_crosscheck_facets(&mut env);
        let err = elaborate_ensures_in(
            "(result as int) == big_int(a as int)",
            &[("a", "u128")],
            "big",
            &facets,
            &ProofClauseInputs::proof_lift(None),
        )
        .expect_err("no second read must fail closed");
        assert!(err.contains("second, independent read"), "got: {err}");
    }

    // ------------------------------------------------------- the refusals

    /// D-1: a signed value has no `Nat`, and the message says what to do.
    #[test]
    fn d1_signed_to_nat_is_refused_with_options() {
        let mut env = Environment::with_prelude();
        let mut facets = FacetTable::new();
        declare_island_def(
            &mut env,
            &mut facets,
            "nat_id",
            "nat_id_def",
            &[Domain::Nat],
            &Domain::Nat,
            Expr::bvar(0),
        );
        let f = admit_projection_function(&mut env, "f_def", &[i64d()], 0).expect("mints");
        facets.insert("f", admissible());
        facets.admit("f", f.with_declared_signature(Some(i64d()), None));

        let err = lifted("nat_id(x as nat) == (r as nat)", &[("x", "i64"), ("r", "u64")], "f", "i64", &facets)
            .expect_err("`i64 as nat` must be refused");
        assert!(err.contains("`i64`"), "names the type: {err}");
        assert!(err.contains("18446744073709551615"), "says why the bit pattern is wrong: {err}");
        assert!(err.contains("as int"), "offers the concrete alternative: {err}");
    }

    /// D-2: an unbounded term is never narrowed to a machine carrier, and the
    /// note gives the wrap witness.
    #[test]
    fn d2_narrowing_is_refused_with_the_wrap_witness() {
        let mut env = Environment::with_prelude();
        let mut facets = FacetTable::new();
        declare_island_def(
            &mut env,
            &mut facets,
            "nat_id",
            "nat_id_def",
            &[Domain::Nat],
            &Domain::Nat,
            Expr::bvar(0),
        );
        // A `UInt64`-declared island definition taking the lifted term.
        declare_island_def(
            &mut env,
            &mut facets,
            "u_id",
            "u_id_def",
            &[u64d()],
            &u64d(),
            Expr::bvar(0),
        );
        let f = admit_projection_function(&mut env, "f_def", &[u64d()], 0).expect("mints");
        facets.insert("f", admissible());
        facets.admit("f", f.with_declared_signature(Some(u64d()), None));

        let err = lifted(
            "u_id(nat_id(x as nat)) == result",
            &[("x", "u64")],
            "f",
            "u64",
            &facets,
        )
        .expect_err("a Nat term at a UInt64 parameter must be refused");
        assert!(err.contains("never narrowed"), "names the refusal: {err}");
        assert!(err.contains("UInt64.ofNat"), "gives the wrap witness: {err}");
        // The load-bearing half, and the half a message built from `from`/`to`
        // alone CANNOT carry: the DECLARED carrier that could not be reached.
        // Before this assertion the message read "`nat_id(x as nat)` is a `nat`
        // term where a `nat` is declared", which is a tautology — it passed the
        // two assertions above because both live in the constant part of the
        // format string.
        assert!(
            err.contains("the declared carrier is `UInt64`"),
            "names the DECLARED machine carrier, not the math type twice: {err}"
        );
        assert!(err.contains("is a `nat` term"), "names what the term is: {err}");
    }

    /// D-2 at the OTHER call site: a cast sitting at a MACHINE position
    /// (`u_id(x as nat)` — the cast's value is a `Nat`, the parameter is
    /// `UInt64`). Before this test the branch had no coverage at all, and it is
    /// the one whose declared carrier comes from the ambient domain rather than
    /// from a `DeclaredCarriers` row.
    #[test]
    fn d2_a_cast_at_a_machine_position_names_that_machine_carrier() {
        let mut env = Environment::with_prelude();
        let mut facets = FacetTable::new();
        declare_island_def(
            &mut env,
            &mut facets,
            "u8_id",
            "u8_id_def",
            &[Domain::Machine(MachineUIntWidth::U8)],
            &Domain::Machine(MachineUIntWidth::U8),
            Expr::bvar(0),
        );
        let f = admit_projection_function(
            &mut env,
            "g_def",
            &[Domain::Machine(MachineUIntWidth::U8)],
            0,
        )
        .expect("mints");
        facets.insert("g", admissible());
        facets.admit(
            "g",
            f.with_declared_signature(Some(Domain::Machine(MachineUIntWidth::U8)), None),
        );

        let err = lifted("u8_id(x as nat) == result", &[("x", "u8")], "g", "u8", &facets)
            .expect_err("a `nat`-valued cast at a `UInt8` parameter must be refused");
        assert!(err.contains("never narrowed"), "names the refusal: {err}");
        // The WIDTH follows the declared carrier: a hardcoded `2^64` here would
        // be a false witness about a `UInt8` parameter.
        assert!(
            err.contains("the declared carrier is `UInt8`"),
            "names the declared carrier: {err}"
        );
        assert!(err.contains("UInt8.ofNat"), "the wrap witness is at the DECLARED width: {err}");
        assert!(err.contains("2^8"), "the modulus is the declared width's: {err}");
    }

    /// D-3: arithmetic that mixes a math operand with a machine one.
    #[test]
    fn d3_mixed_arithmetic_is_refused() {
        let mut env = Environment::with_prelude();
        let mut facets = FacetTable::new();
        declare_island_def(
            &mut env,
            &mut facets,
            "nat_id",
            "nat_id_def",
            &[Domain::Nat],
            &Domain::Nat,
            Expr::bvar(0),
        );
        let f = admit_projection_function(&mut env, "f_def", &[u64d(), u64d()], 0).expect("mints");
        facets.insert("f", admissible());
        facets.admit("f", f.with_declared_signature(Some(u64d()), None));

        let err = lifted(
            "nat_id(x as nat) + y == (result as nat)",
            &[("x", "u64"), ("y", "u64")],
            "f",
            "u64",
            &facets,
        )
        .expect_err("mixed arithmetic must be refused");
        // Pin the REASON, not a word that also lives in D-2's note and in
        // several pre-existing diagnostics of this crate.
        assert!(err.contains("mixes"), "names the defect: {err}");
        assert!(err.contains("nat") && err.contains("u64"), "names both operand types: {err}");
        assert!(err.contains("WRAPS") || err.contains("wrap"), "says why: {err}");
    }

    /// D-9: only `as nat` and `as int` are spec casts.
    #[test]
    fn d9_a_machine_to_machine_cast_is_not_a_spec_cast() {
        let mut env = Environment::with_prelude();
        let mut facets = FacetTable::new();
        let f = admit_projection_function(&mut env, "f_def", &[u64d()], 0).expect("mints");
        facets.insert("f", admissible());
        facets.admit("f", f.with_declared_signature(Some(u64d()), None));
        let err = lifted("(x as u32) == result", &[("x", "u64")], "f", "u64", &facets)
            .expect_err("`as u32` must be refused");
        assert!(err.contains("not a spec cast"), "got: {err}");
        assert!(err.contains("as nat") && err.contains("as int"), "names what IS one: {err}");
    }

    /// D-12: pointer-width integers are outside the table, and the message
    /// explains the measured reason rather than calling it unimplemented.
    #[test]
    fn d12_pointer_width_is_refused_with_the_reason() {
        let mut env = Environment::with_prelude();
        let mut facets = FacetTable::new();
        declare_island_def(
            &mut env,
            &mut facets,
            "nat_id",
            "nat_id_def",
            &[Domain::Nat],
            &Domain::Nat,
            Expr::bvar(0),
        );
        let f = admit_projection_function(&mut env, "f_def", &[u64d()], 0).expect("mints");
        facets.insert("f", admissible());
        facets.admit("f", f.with_declared_signature(Some(u64d()), None));
        let err = lifted(
            "nat_id(p as nat) == (result as nat)",
            &[("p", "usize64")],
            "f",
            "u64",
            &facets,
        )
        .expect_err("a pointer-width lift must be refused");
        assert!(err.contains("pointer-width"), "names the class: {err}");
        assert!(err.contains("32-bit target"), "gives the measured reason: {err}");
    }

    /// D-11: a machine term at a math position with no cast. The implicit lift
    /// is decision OR-1, so the refusal prints the cast to write and names
    /// the missing ruling's effect rather than silently inserting it.
    #[test]
    fn d11_an_uncast_machine_term_at_a_math_position_prints_the_cast() {
        let mut env = Environment::with_prelude();
        let mut facets = FacetTable::new();
        declare_island_def(
            &mut env,
            &mut facets,
            "nat_id",
            "nat_id_def",
            &[Domain::Nat],
            &Domain::Nat,
            Expr::bvar(0),
        );
        let f = admit_projection_function(&mut env, "f_def", &[u64d(), u64d()], 0).expect("mints");
        facets.insert("f", admissible());
        facets.admit("f", f.with_declared_signature(Some(u64d()), None));

        // One argument lifted, the other not.
        let err = lifted(
            "nat_id(x as nat) == (y as nat)",
            &[("x", "u64"), ("y", "u64")],
            "f",
            "u64",
            &facets,
        )
        .expect("both sides ARE cast here — sanity")
        .goal;
        let _ = err;

        let err = lifted("nat_id(x as nat) <= y", &[("x", "u64"), ("y", "u64")], "f", "u64", &facets)
            .expect_err("an uncast machine side at a Nat relation must be refused");
        assert!(err.contains("never coerced"), "keeps the standing sentence: {err}");
        assert!(err.contains("OR-1"), "names the missing ruling: {err}");
        assert!(err.contains("y as nat"), "prints the cast to write: {err}");
    }

    /// The RELATION path must not give advice that cannot be taken.
    ///
    /// `(x as nat) == y` with `y: i64` used to print "write the lift
    /// explicitly: `y as nat`" unconditionally — and `y as nat` is D-1, whose
    /// whole point is that reading the bit pattern turns `-1` into `2^64 - 1`.
    /// The call-argument path always consulted the lift table before advising;
    /// this pins that the relation path does too.
    #[test]
    fn the_relation_path_advises_only_a_cast_the_table_actually_has() {
        let mut env = Environment::with_prelude();
        let mut facets = FacetTable::new();
        let f = admit_projection_function(&mut env, "f_def", &[u64d(), i64d()], 0).expect("mints");
        facets.insert("f", admissible());
        facets.admit("f", f.with_declared_signature(Some(u64d()), None));

        let err = lifted(
            "(x as nat) == y",
            &[("x", "u64"), ("y", "i64")],
            "f",
            "u64",
            &facets,
        )
        .expect_err("a signed operand at a `nat` relation must be refused");
        // The load-bearing distinction: D-1 NAMES the refused spelling in its
        // lead (`\`y as nat\`: \`y\` is an \`i64\` …`) and then says it has no
        // `Nat` value; D-11 would have ADVISED writing it
        // ("help: write the lift explicitly: `y as nat`"). Before the fix this
        // site returned D-11 unconditionally, so the author was told to write a
        // cast the table refuses.
        assert!(
            !err.contains("write the lift explicitly"),
            "the refusal must NOT advise a cast the table refuses: {err}"
        );
        assert!(!err.contains("OR-1"), "and it is not the D-11 owner-ruling refusal: {err}");
        assert!(err.contains("has no `Nat` value"), "it is D-1, by its reason: {err}");
        assert!(err.contains("y as int"), "and it offers the route that exists: {err}");
    }

    // ------------------------------------------------------- corpus control

    /// §5.5: at `ClauseMode::Strict` — which is every pre-existing entry point
    /// — a cast is the SAME `unsupported term shape` it always was. The mode is
    /// the gate, so no existing elaboration can be retyped by this work.
    #[test]
    fn strict_mode_still_refuses_a_cast_with_the_pre_existing_message() {
        let mut env = Environment::with_prelude();
        let mut facets = FacetTable::new();
        declare_island_def(
            &mut env,
            &mut facets,
            "nat_id",
            "nat_id_def",
            &[Domain::Nat],
            &Domain::Nat,
            Expr::bvar(0),
        );
        let f = admit_projection_function(&mut env, "f_def", &[u64d()], 0).expect("mints");
        facets.insert("f", admissible());
        facets.admit("f", f.with_declared_signature(Some(u64d()), None));
        let err = elaborate_ensures("(x as nat) == result", &[("x", "u64")], "f", &facets)
            .expect_err("Strict must refuse the cast");
        assert!(
            err.contains("unsupported term shape"),
            "the pre-existing message, unchanged: {err}"
        );

        // ... and the SAME clause in `ProofLift` is accepted only as far as the
        // table allows: the right-hand side is an uncast `u64`, so it is D-11,
        // not a silent implicit lift.
        let lifted_err = lifted("(x as nat) == result", &[("x", "u64")], "f", "u64", &facets)
            .expect_err("the uncast side must still be refused");
        assert!(lifted_err.contains("OR-1"), "and it names the missing ruling: {lifted_err}");
    }

    /// A literal argument at a math-declared parameter takes the DECLARED
    /// domain, not its sibling's machine width. `nat_snd(x as nat, 300)` from a
    /// `u8` function is the design's pinned case: today the literal is typed
    /// `u8` by its sibling and `300` is out of range.
    #[test]
    fn a_literal_argument_takes_the_declared_math_domain() {
        let mut env = Environment::with_prelude();
        let mut facets = FacetTable::new();
        declare_island_def(
            &mut env,
            &mut facets,
            "nat_snd",
            "nat_snd_def",
            &[Domain::Nat, Domain::Nat],
            &Domain::Nat,
            Expr::bvar(0),
        );
        let u8d = Domain::Machine(MachineUIntWidth::U8);
        let f = admit_projection_function(&mut env, "f_def", &[u8d.clone()], 0).expect("mints");
        facets.insert("f", admissible());
        facets.admit("f", f.with_declared_signature(Some(u8d), None));

        let clause = lifted(
            "nat_snd(x as nat, 300) == (result as nat)",
            &[("x", "u8")],
            "f",
            "u8",
            &facets,
        )
        .expect("the literal must be read at `Nat`");
        let _ = TypeChecker::new(&env).infer_sort(&clause.goal).expect("well-typed");
        assert!(
            format!("{}", clause.goal).contains("300"),
            "the literal must survive as the Nat numeral 300"
        );
    }

    /// THE UN-CAST-GATED BRANCH, measured. The literal-argument row is gated on
    /// `ambient_proof_lift().is_some()` alone, NOT on `contains_cast`, so it
    /// fires on an atom with no cast anywhere — which is every user `ensures`
    /// clause the compiler now elaborates. Both reviewers flagged the lane's
    /// "an atom must CONTAIN a `Cast` node for any new branch to fire" as
    /// false; it is, and this is the measurement that replaces the claim.
    ///
    /// The direction is error → success only: under the pre-existing rule the
    /// literal took its SIBLING's `u8` domain, `255` was in range but `300` was
    /// not, and the clause was refused. `contains_cast` is nowhere in this
    /// clause.
    #[test]
    fn the_uncast_literal_row_is_a_real_mode_difference_and_only_widens() {
        let mut env = Environment::with_prelude();
        let mut facets = FacetTable::new();
        let u8d = Domain::Machine(MachineUIntWidth::U8);
        // `def shrink (a : UInt32) : UInt8 := UInt8.ofNat (UInt32.toNat a)` —
        // the call's RESULT carrier is the atom's, so nothing but the literal's
        // domain is in question.
        declare_island_def(
            &mut env,
            &mut facets,
            "shrink",
            "shrink_def",
            &[u32d()],
            &u8d,
            Expr::app(c("UInt8.ofNat"), Expr::app(c("UInt32.toNat"), Expr::bvar(0))),
        );
        let f = admit_projection_function(&mut env, "f_def", &[u8d.clone()], 0).expect("mints");
        facets.insert("f", admissible());
        facets.admit("f", f.with_declared_signature(Some(u8d), None));

        // No cast anywhere in this clause.
        let clause_src = "result == shrink(300)";
        assert!(!clause_src.contains(" as "), "the point is that there is no cast here");

        let strict = elaborate_ensures(clause_src, &[("x", "u8")], "f", &facets);
        let lifted_goal = lifted(clause_src, &[("x", "u8")], "f", "u8", &facets);
        // Strict: the literal has no domain of its own, so it takes the
        // AMBIENT one — `u8`, from `result` — and 300 is out of range there.
        let strict_err = strict.expect_err("Strict must refuse the literal at the ambient width");
        // MEASURED (2026-09-18): the sibling/ambient domain decides the
        // literal's CARRIER before any range check runs, so the pre-existing
        // refusal is the "never coerced" one, naming `UInt32` against a `u8`
        // term — not an out-of-range message. Pinned as measured rather than as
        // predicted.
        assert!(
            strict_err.contains("never coerced")
                && strict_err.contains("UInt32")
                && strict_err.contains("`u8` term"),
            "the pre-existing refusal is the ambient-decided carrier: {strict_err}"
        );
        // ProofLift: `300` takes the DECLARED `UInt32` parameter's unique
        // preimage and is in range. THIS FIRES WITH NO CAST IN THE CLAUSE.
        let clause = lifted_goal.expect("ProofLift reads the literal at the declared width");
        let _ = TypeChecker::new(&env).infer_sort(&clause.goal).expect("well-typed");
        assert!(
            clause.required_signed_lift_widths.is_empty(),
            "no seeded model is involved in a plain literal row"
        );
    }

    /// THE PROOFLIFT CORPUS CONTROL the design specified and the lane replaced
    /// with a by-construction argument its own code does not satisfy.
    ///
    /// Every user `ensures` clause the compiler elaborates now runs at
    /// `ClauseMode::ProofLift`, so "the 117 pre-existing tests pass at Strict"
    /// is a control for a mode nothing uses any more. This runs a batch of
    /// cast-free clause shapes through BOTH entries and demands BYTE-IDENTICAL
    /// goals: relations, arithmetic, an admitted call, a nested call, a literal
    /// that is in range at its sibling's width, a boolean, and a `result`
    /// projection.
    #[test]
    fn the_mode_change_is_byte_identical_on_the_uncast_corpus() {
        let mut env = Environment::with_prelude();
        let mut facets = FacetTable::new();
        let u64 = u64d();
        declare_island_def(
            &mut env,
            &mut facets,
            "isl_id",
            "isl_id_def",
            &[u64.clone()],
            &u64,
            Expr::bvar(0),
        );
        declare_island_def(
            &mut env,
            &mut facets,
            "isl_snd",
            "isl_snd_def",
            &[u64.clone(), u64.clone()],
            &u64,
            Expr::bvar(0),
        );
        let f = admit_projection_function(&mut env, "f_def", &[u64.clone(), u64.clone()], 0)
            .expect("mints");
        facets.insert("f", admissible());
        facets.admit("f", f.with_declared_signature(Some(u64.clone()), None));

        let params = [("x", "u64"), ("y", "u64")];
        let corpus = [
            "result == x",
            "result == isl_id(x)",
            "result == isl_snd(x, y)",
            "result == isl_snd(isl_id(x), 7)",
            "result == isl_id(7)",
            "isl_id(x) == result",
            "result >= x",
            "result <= y",
            "result != y",
            "x < y",
            "result == x + y",
            "result == x * 2",
            "(result == x) || (result == y)",
            "(result >= x) && (result >= y)",
        ];
        let mut agreed = 0;
        for clause in corpus {
            assert!(!clause.contains(" as "), "the corpus is cast-free by construction");
            let strict = elaborate_ensures(clause, &params, "f", &facets);
            let proof = lifted(clause, &params, "f", "u64", &facets).map(|c| c.goal);
            match (strict, proof) {
                (Ok(a), Ok(b)) => {
                    assert_eq!(
                        format!("{a}"),
                        format!("{b}"),
                        "the mode must not retype `{clause}`"
                    );
                    agreed += 1;
                }
                (Err(a), Err(_)) => {
                    // Error → error is allowed (the text may differ; see
                    // `contains_cast`'s doc), but a clause that FAILS today and
                    // SUCCEEDS under the mode is a silent capability change and
                    // must be a named test, not corpus noise.
                    let _ = a;
                }
                (Ok(a), Err(b)) => {
                    panic!("ProofLift lost a clause that elaborates today: `{clause}`\n{a}\n{b}")
                }
                (Err(a), Ok(_)) => panic!(
                    "ProofLift silently accepted a cast-free clause Strict refuses: \
                     `{clause}`\n{a}"
                ),
            }
        }
        assert!(agreed >= 12, "the control must actually elaborate its corpus: {agreed}/14");

        // Trust (d1, 2026-09-28): the SAME corpus through the ∀-`result` entry —
        // `result` a free variable typed from the signature table, no self
        // function — which is the reading the E9 citation sweep falls back to
        // when the postcondition goal cannot be built (always, with
        // verification off). That fallback used to run at `Strict` while the
        // discharge rung ran at `ProofLift`; it now runs at the discharge rung's
        // mode, so this is the control that the switch retypes no cast-free
        // clause and admits none Strict refuses. The bindings are selected
        // exactly as the sweep selects them (`exact_typed_bindings_for_clause`
        // over the whole signature table, `result` included).
        let signature = [("x", "u64"), ("y", "u64"), ("result", "u64")];
        let mut fallback_agreed = 0;
        for clause in corpus {
            let bound = exact_typed_bindings_for_clause(clause, &signature)
                .unwrap_or_else(|e| panic!("the corpus binds exactly: `{clause}`: {e}"));
            let var_types: Vec<(&str, &str)> =
                bound.iter().map(|(n, t)| (n.as_str(), t.as_str())).collect();
            let strict =
                elaborate_goal_typed_in(trust_symbols::Capability::Proof, clause, &var_types, &facets);
            let proof = elaborate_goal_typed_in_mode(
                trust_symbols::Capability::Proof,
                clause,
                &var_types,
                &facets,
                &ProofClauseInputs::proof_lift(Some("u64")),
                None,
            );
            match (strict, proof) {
                (Ok(a), Ok(b)) => {
                    assert_eq!(
                        format!("{a}"),
                        format!("{}", b.goal),
                        "the fallback's mode must not retype `{clause}`"
                    );
                    assert!(
                        b.required_signed_lift_widths.is_empty(),
                        "a cast-free clause seeds nothing: `{clause}`"
                    );
                    fallback_agreed += 1;
                }
                (Err(_), Err(_)) => {}
                (Ok(a), Err(b)) => panic!(
                    "the ProofLift fallback lost a clause the Strict one elaborates: \
                     `{clause}`\n{a}\n{b}"
                ),
                (Err(a), Ok(_)) => panic!(
                    "the ProofLift fallback silently accepted a cast-free clause Strict refuses: \
                     `{clause}`\n{a}"
                ),
            }
        }
        assert!(
            fallback_agreed >= 12,
            "the fallback control must actually elaborate its corpus: {fallback_agreed}/14"
        );
    }

    /// Trust (d1, 2026-09-28): the ∀-`result` entry at the two modes on the
    /// shape that broke — a cited `ensures` whose call argument is an explicit
    /// lift. At `ProofLift` it elaborates to a well-typed goal (the lift is
    /// read); at `Strict` it is refused, and — the B2 half — the refusal names
    /// the CAST, never "the argument is a `u64` term": `argument_domain` looks
    /// through a cast, so the carrier check used to describe `x as nat` as the
    /// bare `x`.
    #[test]
    fn the_forall_result_entry_reads_a_lift_only_in_proof_lift_and_never_misnames_it() {
        let mut env = Environment::with_prelude();
        let mut facets = FacetTable::new();
        // clean { def nat_to_u64 (n : Nat) : UInt64 := UInt64.ofNat n }
        declare_island_def(
            &mut env,
            &mut facets,
            "nat_to_u64",
            "nat_to_u64_def",
            &[Domain::Nat],
            &u64d(),
            Expr::app(c("UInt64.ofNat"), Expr::bvar(0)),
        );
        let clause_src = "result == nat_to_u64(x as nat)";
        let var_types = [("result", "u64"), ("x", "u64")];

        let strict = elaborate_goal_typed_in(
            trust_symbols::Capability::Proof,
            clause_src,
            &var_types,
            &facets,
        )
        .expect_err("Strict never reads a cast");
        assert!(
            strict.starts_with("unsupported term shape"),
            "the pre-existing head, so no consumer keyed on it moves: {strict}"
        );
        assert!(strict.contains("x as nat"), "the refusal names the cast the author wrote: {strict}");
        assert!(
            !strict.contains("`u64` term") && !strict.contains("never coerced"),
            "B2: Strict must not describe `x as nat` as its operand's machine type: {strict}"
        );

        let proof = elaborate_goal_typed_in_mode(
            trust_symbols::Capability::Proof,
            clause_src,
            &var_types,
            &facets,
            &ProofClauseInputs::proof_lift(Some("u64")),
            None,
        )
        .expect("ProofLift reads the explicit lift in the ∀-`result` reading");
        let _ = TypeChecker::new(&env).infer_sort(&proof.goal).expect("well-typed");
        assert!(
            format!("{}", proof.goal).contains("UInt64.toNat"),
            "the argument is lifted by the exact injection: {}",
            proof.goal
        );
        assert!(proof.required_signed_lift_widths.is_empty(), "an unsigned lift seeds nothing");

        // The mode is scoped to the one elaboration: the next Strict call is
        // Strict again, with the same refusal.
        let again = elaborate_goal_typed_in(
            trust_symbols::Capability::Proof,
            clause_src,
            &var_types,
            &facets,
        )
        .expect_err("no leaked ProofLift context");
        assert_eq!(again, strict, "Strict is byte-stable across a ProofLift elaboration");
    }

    /// POINTER-WIDTH BINDERS, at the spelling the compiler actually sends.
    ///
    /// The lane shipped `LiftRefusal::PointerWidth` (D-12) and three documents
    /// saying `usize`/`isize` are refused. They are not: every E9 discharge
    /// lane resolves its binder table through
    /// [`discharge_binding_ty_for_target`] BEFORE the elaborator sees it, so a
    /// `usize` parameter arrives spelled `u64` on a 64-bit target and DOES
    /// lift. `Domain::USize` reaches `lift_for` only from the statement-only
    /// lanes, which carry the `usize64` spelling.
    ///
    /// This measures the reachable path on both sides of the resolution.
    #[test]
    fn a_pointer_sized_binder_lifts_at_the_targets_resolved_width() {
        let mut env = Environment::with_prelude();
        let mut facets = FacetTable::new();
        declare_island_def(
            &mut env,
            &mut facets,
            "nat_id",
            "nat_id_def",
            &[Domain::Nat],
            &Domain::Nat,
            Expr::bvar(0),
        );
        let f = admit_projection_function(&mut env, "f_def", &[u64d()], 0).expect("mints");
        facets.insert("f", admissible());
        facets.admit("f", f.with_declared_signature(Some(u64d()), None));

        // What the compiler sends: `trust_fn_discharge_binder_types` rewrote
        // `usize` to the target's fixed width first.
        let resolved = discharge_binding_ty_for_target("usize", TargetPointerWidth::W64);
        assert_eq!(resolved, "u64", "this is the spelling the discharge lanes emit");
        let clause = lifted(
            "(result as nat) == nat_id(p as nat)",
            &[("p", resolved)],
            "f",
            resolved,
            &facets,
        )
        .expect("a target-resolved pointer-sized binder lifts");
        let _ = TypeChecker::new(&env).infer_sort(&clause.goal).expect("well-typed");
        assert!(
            format!("{}", clause.goal).contains("UInt64.toNat"),
            "and it lifts at the RESOLVED width: {}",
            clause.goal
        );

        // The un-resolved spelling — what the STATEMENT-ONLY lanes (runtime
        // monitors, the zero-authority denotation row) keep — has no lift row.
        // That is D-12, and this is the only family that can reach it.
        let err = lifted(
            "(result as nat) == nat_id(p as nat)",
            &[("p", "usize64")],
            "f",
            "u64",
            &facets,
        )
        .expect_err("the statement-only spelling has no lift row");
        assert!(err.contains("pointer-width integer"), "D-12 names the refusal: {err}");
    }

    /// The 32-bit half of the same story, and the reason the row is safe: on a
    /// pointer width where the E6 mint's FIXED unsigned record disagrees with
    /// the target-resolved binder, the self cross-check refuses rather than
    /// lifting at the wrong width.
    #[test]
    fn a_pointer_sized_return_fails_closed_when_the_two_reads_disagree() {
        let mut env = Environment::with_prelude();
        let mut facets = FacetTable::new();
        declare_island_def(
            &mut env,
            &mut facets,
            "nat_id",
            "nat_id_def",
            &[Domain::Nat],
            &Domain::Nat,
            Expr::bvar(0),
        );
        // The mint records an unsigned pointer-sized return at a FIXED 64-bit
        // domain on EVERY target (`ty_to_domain`), so on a 32-bit target it
        // says `u64` …
        let f = admit_projection_function(&mut env, "f_def", &[u64d()], 0).expect("mints");
        facets.insert("f", admissible());
        facets.admit("f", f.with_declared_signature(Some(u64d()), None));
        // … while `trust_fn_discharge_binder_types` resolves the same `usize`
        // return to `u32`.
        let resolved = discharge_binding_ty_for_target("usize", TargetPointerWidth::W32);
        assert_eq!(resolved, "u32");

        let err = lifted(
            "(result as nat) == nat_id(p as nat)",
            &[("p", "u64")],
            "f",
            resolved,
            &facets,
        )
        .expect_err("the two reads disagree, so the lift must fail closed");
        assert!(
            err.contains("recorded result domain") || err.contains("disagree"),
            "and the refusal is the two-read cross-check: {err}"
        );
    }

    /// A NESTED lift: `(x as nat) as int` composes to `Int.ofNat (toNat x)`.
    #[test]
    fn a_nat_term_lifts_on_to_int() {
        let mut env = Environment::with_prelude();
        let mut facets = FacetTable::new();
        declare_island_def(
            &mut env,
            &mut facets,
            "int_id",
            "int_id_def",
            &[Domain::Int],
            &Domain::Int,
            Expr::bvar(0),
        );
        let f = admit_projection_function(&mut env, "f_def", &[u64d()], 0).expect("mints");
        facets.insert("f", admissible());
        facets.admit("f", f.with_declared_signature(Some(u64d()), None));

        let clause = lifted(
            "int_id((x as nat) as int) == ((result as nat) as int)",
            &[("x", "u64")],
            "f",
            "u64",
            &facets,
        )
        .expect("Nat -> Int composes");
        let of_nat = |e: Expr| Expr::app(c("Int.ofNat"), e);
        let to_nat = |e: Expr| Expr::app(c("UInt64.toNat"), e);
        let expected = Expr::pi(
            BinderInfo::Default,
            c("UInt64"),
            Domain::Int.eq(
                Expr::app(c("int_id_def"), of_nat(to_nat(Expr::bvar(0)))),
                of_nat(to_nat(Expr::app(c("f_def"), Expr::bvar(0)))),
            ),
        );
        assert_eq!(clause.goal, expected);
        let _ = TypeChecker::new(&env).infer_sort(&clause.goal).expect("well-typed");
    }

    /// `int as nat` is refused: `Int.toNat` TRUNCATES, and the compiler will
    /// not insert a map that is not injective.
    #[test]
    fn int_to_nat_is_refused() {
        assert_eq!(lift_for(&Domain::Int, MathTy::Nat), Err(LiftRefusal::IntToNat));
        let msg = LiftRefusal::IntToNat.message("k", &Domain::Int, MathTy::Nat);
        assert!(msg.contains("TRUNCATING"), "the note must say why: {msg}");
    }

    /// The table, stated once as a test so a future edit to `lift_for` has to
    /// come past it. Exactness of each accepting row is measured against the
    /// kernel in `tests/nat_lift_probes.rs`.
    #[test]
    fn the_lift_table_is_closed_and_exact() {
        use MachineSIntWidth as S;
        use MachineUIntWidth as U;
        assert_eq!(lift_for(&u64d(), MathTy::Nat), Ok(Lift::UIntToNat(U::U64)));
        assert_eq!(lift_for(&Domain::U128, MathTy::Nat), Ok(Lift::BitVecToNat));
        assert_eq!(
            lift_for(&u64d(), MathTy::Int),
            Ok(Lift::UnsignedToInt(Box::new(Lift::UIntToNat(U::U64))))
        );
        assert_eq!(
            lift_for(&Domain::U128, MathTy::Int),
            Ok(Lift::UnsignedToInt(Box::new(Lift::BitVecToNat)))
        );
        assert_eq!(lift_for(&i64d(), MathTy::Int), Ok(Lift::SignedToInt(S::I64)));
        assert_eq!(lift_for(&Domain::Nat, MathTy::Int), Ok(Lift::NatToInt));
        assert_eq!(lift_for(&Domain::Nat, MathTy::Nat), Ok(Lift::Identity));
        assert_eq!(lift_for(&Domain::Int, MathTy::Int), Ok(Lift::Identity));
        // refusals
        assert_eq!(lift_for(&i64d(), MathTy::Nat), Err(LiftRefusal::SignedToNat));
        assert_eq!(lift_for(&Domain::Int, MathTy::Nat), Err(LiftRefusal::IntToNat));
        assert_eq!(
            lift_for(&Domain::USize(TargetPointerWidth::W64), MathTy::Nat),
            Err(LiftRefusal::PointerWidth)
        );
        assert_eq!(
            lift_for(&Domain::ISize(TargetPointerWidth::W32), MathTy::Int),
            Err(LiftRefusal::PointerWidth)
        );
        assert_eq!(lift_for(&Domain::Bool, MathTy::Nat), Err(LiftRefusal::NoLift));
        assert_eq!(
            lift_for(&Domain::OptionSigned(S::I64), MathTy::Int),
            Err(LiftRefusal::NoLift)
        );
        // NOTHING in the table ever narrows: no variant names `ofNat` on the
        // machine side, which is the invariant §5.3 rests on.
        for lift in [
            Lift::Identity,
            Lift::UIntToNat(U::U8),
            Lift::BitVecToNat,
            Lift::UnsignedToInt(Box::new(Lift::UIntToNat(U::U8))),
            Lift::SignedToInt(S::I8),
            Lift::NatToInt,
        ] {
            let rendered = format!("{}", lift.wrap(Expr::bvar(0)).expect("wraps"));
            assert!(
                !rendered.contains("UInt8.ofNat") && !rendered.contains("BitVec.ofNat"),
                "a lift must never narrow: {rendered}"
            );
        }
    }

    /// The seeding obligation is REPORTED, not assumed: a goal that names the
    /// signed lift says so, and a goal that does not says nothing.
    #[test]
    fn the_seeding_obligation_is_reported_per_clause() {
        assert_eq!(Lift::SignedToInt(MachineSIntWidth::I32).required_signed_width(), Some(MachineSIntWidth::I32));
        assert_eq!(Lift::UIntToNat(MachineUIntWidth::U32).required_signed_width(), None);
        assert_eq!(
            Lift::UnsignedToInt(Box::new(Lift::BitVecToNat)).required_signed_width(),
            None
        );
    }
}

#[cfg(test)]
mod requires_hypothesis_tests {
    use super::*;

    /// A candidate hypothesis whose query view agrees with `params`.
    fn hyp(index: usize, text: &str, params: &[(&str, &str)]) -> HypothesisInput {
        HypothesisInput {
            contract_index: index,
            canonical_text: text.to_string(),
            authored_text: text.to_string(),
            query_bindings: params
                .iter()
                .map(|(n, t)| ((*n).to_string(), (*t).to_string()))
                .collect(),
        }
    }

    fn reason_of(row: &HypothesisRow) -> &str {
        match &row.disposition {
            HypothesisDisposition::Omitted { reason } => reason,
            HypothesisDisposition::Bound { .. } => panic!("expected an omission, got a binder"),
        }
    }

    /// `E-allow`, positively and negatively: the whole arithmetic-free fragment
    /// is carried, and nothing outside it is. The negative half is the
    /// false-accept guard — each refused clause has a reading in Clean that
    /// differs from the reading callers are charged, or no pinned reading at
    /// all.
    #[test]
    fn e_allow_admits_exactly_the_arithmetic_free_fragment() {
        let params: &[(&str, &str)] = &[("a", "u64"), ("b", "u64"), ("f", "bool")];
        let build = |text: &str| {
            elaborate_ensures_under_requires(
                "a <= a",
                params,
                "irrelevant_self",
                &FacetTable::new(),
                &[hyp(0, text, params)],
            )
        };
        for admitted in [
            "b <= a",
            "a == b",
            "a != b",
            "a < b && b < a",
            "!(a < b)",
            "f",
            "!f",
            "f == true",
            "a <= 1000",
            "a <= 1000u64",
            "(a <= b) || (b <= a)",
        ] {
            let built =
                build(admitted).unwrap_or_else(|e| panic!("`{admitted}` must be carried: {e}"));
            assert_eq!(built.bound_count(), 1, "`{admitted}` must be carried");
        }
        for (refused, needle) in [
            ("a + b > 10", "`+`"),
            ("a - b > 10", "`-`"),
            ("a * 2 > b", "`*`"),
            ("a / 2 > b", "`/`"),
            ("a % 2 == 0", "`%`"),
            ("a & b == b", "`&`"),
            ("a << 1 > b", "`<<`"),
            ("a as u32 > 3", "cast"),
            ("helper(a) == b", "calls a function"),
            ("a.wrapping_add(b) > 10", "calls a function"),
            ("1 < 2", "no parameter operand"),
            ("a", "not a proposition"),
            ("!a", "not a proposition"),
        ] {
            let err =
                build(refused).err().unwrap_or_else(|| panic!("`{refused}` must NOT be carried"));
            assert!(
                err.contains("eligible"),
                "`{refused}` must leave nothing eligible; got {err}"
            );
            // And the reason, when it is visible beside an eligible companion,
            // must name the cause rather than a generic refusal.
            let mixed = elaborate_ensures_under_requires(
                "a <= a",
                params,
                "irrelevant_self",
                &FacetTable::new(),
                &[hyp(0, refused, params), hyp(1, "b <= a", params)],
            )
            .unwrap_or_else(|e| panic!("`{refused}` beside an eligible clause: {e}"));
            assert_eq!(mixed.bound_count(), 1, "only the eligible clause is carried");
            assert!(
                reason_of(&mixed.hypotheses[0]).contains(needle),
                "the omission of `{refused}` must name `{needle}`; got {}",
                reason_of(&mixed.hypotheses[0])
            );
        }
    }

    /// P-A2: one carried, one omitted — and the row says so. v6/D1: report what
    /// was graded, never a summary of it.
    #[test]
    fn an_omitted_clause_is_disclosed_not_dropped() {
        let params: &[(&str, &str)] = &[("a", "u64"), ("b", "u64")];
        let built = elaborate_ensures_under_requires(
            "a <= a",
            params,
            "irrelevant_self",
            &FacetTable::new(),
            &[hyp(0, "b <= a", params), hyp(1, "a + b > 10", params)],
        )
        .expect("the eligible clause still builds a goal");
        assert_eq!(built.hypotheses.len(), 2, "one row per contract, in contract order");
        assert_eq!(built.hypotheses[0].contract_index, 0);
        assert_eq!(
            built.hypotheses[0].disposition,
            HypothesisDisposition::Bound { binder_index: 0 }
        );
        assert!(reason_of(&built.hypotheses[1]).contains("`+`"));
        assert_eq!(built.bound_texts(), vec!["b <= a"]);
    }

    /// The hypothesis is derived from the QUERY-OWNED proposition. A clause
    /// whose query view disagrees with the signature — the one failure the
    /// kernel cannot catch, because the goal still types — is omitted, not
    /// reconciled. An ABSENT query view is not "no opinion" either.
    #[test]
    fn a_query_view_that_disagrees_with_the_signature_is_omitted() {
        let params: &[(&str, &str)] = &[("a", "u64"), ("b", "u64")];
        let disagreeing = HypothesisInput {
            contract_index: 0,
            canonical_text: "b <= a".to_string(),
            authored_text: "b <= a".to_string(),
            query_bindings: vec![("a".into(), "u32".into()), ("b".into(), "u64".into())],
        };
        let err = elaborate_ensures_under_requires(
            "a <= a",
            params,
            "irrelevant_self",
            &FacetTable::new(),
            &[disagreeing],
        )
        .expect_err("a disagreeing carrier must not be carried");
        assert!(err.contains("eligible"), "got {err}");

        let missing = HypothesisInput {
            contract_index: 0,
            canonical_text: "b <= a".to_string(),
            authored_text: "b <= a".to_string(),
            query_bindings: Vec::new(),
        };
        let mixed = elaborate_ensures_under_requires(
            "a <= a",
            params,
            "irrelevant_self",
            &FacetTable::new(),
            &[missing, hyp(1, "a <= b", params)],
        )
        .expect("the well-formed companion still builds");
        assert!(
            reason_of(&mixed.hypotheses[0]).contains("publishes no carrier"),
            "an absent query view is not 'no opinion': {}",
            reason_of(&mixed.hypotheses[0])
        );
    }

    /// A hypothesis may introduce a binder the conclusion never mentions, and it
    /// is appended in SIGNATURE order — never in the order the clauses happen to
    /// be authored, which would make the goal depend on contract order.
    #[test]
    fn extra_hypothesis_variables_are_appended_in_signature_order() {
        let params: &[(&str, &str)] = &[("a", "u64"), ("b", "u64"), ("c", "u64")];
        let built = elaborate_ensures_under_requires(
            "a <= a",
            params,
            "irrelevant_self",
            &FacetTable::new(),
            // Authored `c` first; the signature order is `b` then `c`.
            &[hyp(0, "c <= a", params), hyp(1, "b <= a", params)],
        )
        .expect("both clauses are eligible");
        assert_eq!(built.value_binders, vec!["a", "b", "c"]);
        assert_eq!(built.bound_count(), 2);
    }

    /// The E3 quantifier fragment authors its own binders, so no second rung is
    /// built for it — and the refusal says why rather than silently returning
    /// the unconditional goal under the conditional name.
    #[test]
    fn a_quantified_ensures_has_no_second_rung() {
        let params: &[(&str, &str)] = &[("a", "u64"), ("b", "u64")];
        let err = elaborate_ensures_under_requires(
            "forall i: u64, i >= i",
            params,
            "irrelevant_self",
            &FacetTable::new(),
            &[hyp(0, "b <= a", params)],
        )
        .expect_err("a quantified clause must not get a second rung");
        assert!(err.contains("quantifier"), "got {err}");
    }

    /// Zero eligible candidates is an `Err`, never `G0` wearing `G1`'s name: a
    /// caller must not be able to spend a second kernel grade on the goal it has
    /// already graded and report it as a conditional discharge.
    #[test]
    fn a_goal_with_no_hypotheses_is_refused_rather_than_returned() {
        let params: &[(&str, &str)] = &[("a", "u64")];
        let err = elaborate_ensures_under_requires(
            "a <= a",
            params,
            "irrelevant_self",
            &FacetTable::new(),
            &[],
        )
        .expect_err("no candidates means no second rung");
        assert!(err.contains("eligible"), "got {err}");
    }

    /// Peel `count` `Pi` binders off `e`, panicking if there are fewer.
    fn peel_pis(e: &Expr, count: usize) -> Expr {
        let mut node = e.clone();
        for step in 0..count {
            let clean_kernel::ExprKind::Pi(_, _, body) = node.kind() else {
                panic!("expected at least {count} Pi binders; only {step} were present: {e}");
            };
            let next = (**body).clone();
            node = next;
        }
        node
    }

    /// The conclusion `G1` states is the one `G0` states — they share the whole
    /// rewrite prefix, so a change to one cannot drift from the other.
    ///
    /// STRUCTURALLY, not by string suffix. The first version of this test
    /// compared `g1.to_string()` against G0's last `->`-separated segment, which
    /// a conclusion containing its own `->` defeats and which compares no binder
    /// at all. This peels the two telescopes and compares the `Expr`s: `G1`'s
    /// conclusion must be `G0`'s conclusion under `n` more binders, which is
    /// exactly `lift(n)`. A drift of one operator, one binder or one de Bruijn
    /// index fails it.
    #[test]
    fn g0_and_g1_state_the_same_conclusion() {
        // A conclusion whose own rendering contains `->`: `!(a <= b)` elaborates
        // through `Not`, which Clean prints as an arrow into `False`. The old
        // suffix test could not tell this conclusion from a hypothesis.
        for clause in ["a <= b", "!(a <= b)", "a <= b || b <= a"] {
            let params: &[(&str, &str)] = &[("a", "u64"), ("b", "u64")];
            let facets = FacetTable::new();
            let g0 = elaborate_ensures(clause, params, "irrelevant_self", &facets)
                .unwrap_or_else(|e| panic!("`{clause}`: the unconditional goal builds: {e}"));
            let g1 = elaborate_ensures_under_requires(
                clause,
                params,
                "irrelevant_self",
                &facets,
                &[hyp(0, "b <= a", params), hyp(1, "a <= b", params)],
            )
            .unwrap_or_else(|e| panic!("`{clause}`: the conditional goal builds: {e}"));

            // The value-binder prefix is G0's, in G0's order.
            assert_eq!(g1.value_binders, vec!["a".to_string(), "b".to_string()], "{clause}");
            assert_eq!(g1.bound_count(), 2, "{clause}");

            let n_values = g1.value_binders.len();
            let n_hyps = g1.bound_count();
            let g0_conclusion = peel_pis(&g0, n_values);
            let g1_conclusion = peel_pis(&g1.goal, n_values + n_hyps);
            assert_eq!(
                g1_conclusion,
                g0_conclusion.lift(u32::try_from(n_hyps).expect("two")),
                "`{clause}`: G1's conclusion must be G0's conclusion under {n_hyps} more \
                 binders\n G0 = {g0}\n G1 = {}",
                g1.goal
            );
        }
    }

    /// THE INVARIANT OF §2.3, with teeth: only `canonical_text` is ever
    /// elaborated. `authored_text` is real source text in production (the
    /// compiler fills it from `span_to_snippet`), so the two genuinely differ,
    /// and an implementation that read the authored spelling would build a
    /// DIFFERENT hypothesis from the one callers are charged. Every other test
    /// in this module sets the two fields to the same string and so cannot tell
    /// the two apart.
    #[test]
    fn only_the_canonical_text_is_elaborated() {
        let params: &[(&str, &str)] = &[("a", "u64"), ("b", "u64")];
        let facets = FacetTable::new();
        // Canonical is eligible, authored is not: the clause MUST be carried,
        // and carried as `b <= a`.
        let carried = elaborate_ensures_under_requires(
            "a <= a",
            params,
            "irrelevant_self",
            &facets,
            &[HypothesisInput {
                contract_index: 0,
                canonical_text: "b <= a".to_string(),
                authored_text: "a + b > 10".to_string(),
                query_bindings: params
                    .iter()
                    .map(|(n, t)| ((*n).to_string(), (*t).to_string()))
                    .collect(),
            }],
        )
        .expect("the CANONICAL spelling is the eligible one");
        assert_eq!(carried.bound_count(), 1);
        assert_eq!(carried.bound_texts(), vec!["b <= a"]);
        let control = elaborate_ensures_under_requires(
            "a <= a",
            params,
            "irrelevant_self",
            &facets,
            &[hyp(0, "b <= a", params)],
        )
        .expect("the control builds");
        assert_eq!(carried.goal, control.goal, "the authored spelling must not reach the goal");

        // And the reverse: an INELIGIBLE canonical spelling is omitted however
        // eligible the authored one looks.
        let omitted = elaborate_ensures_under_requires(
            "a <= a",
            params,
            "irrelevant_self",
            &facets,
            &[
                HypothesisInput {
                    contract_index: 0,
                    canonical_text: "a + b > 10".to_string(),
                    authored_text: "b <= a".to_string(),
                    query_bindings: params
                        .iter()
                        .map(|(n, t)| ((*n).to_string(), (*t).to_string()))
                        .collect(),
                },
                hyp(1, "b <= a", params),
            ],
        )
        .expect("the eligible companion still builds a goal");
        assert_eq!(omitted.bound_count(), 1);
        let reason = reason_of(&omitted.hypotheses[0]);
        assert!(reason.contains("`+`"), "{reason}");
    }

    /// A NEGATIVE literal bound is refused — and the refusal says so, instead of
    /// blaming "a unary operator" the author never typed as one. The capability
    /// gap is real and deliberate: `Formula::Int(-5)` renders as the token `-5`,
    /// and admitting it needs a negative-numeral range argument this lane has
    /// not measured.
    #[test]
    fn a_negative_literal_bound_is_refused_by_name() {
        let params: &[(&str, &str)] = &[("x", "i32"), ("y", "i32")];
        let mixed = elaborate_ensures_under_requires(
            "x <= x",
            params,
            "irrelevant_self",
            &FacetTable::new(),
            &[hyp(0, "x >= -5", params), hyp(1, "y <= x", params)],
        )
        .expect("the eligible companion still builds a goal");
        assert_eq!(mixed.bound_count(), 1);
        let reason = reason_of(&mixed.hypotheses[0]);
        assert!(
            reason.contains("NEGATIVE literal"),
            "the refusal must name the negative literal; got {reason}"
        );
    }

    /// A POINTER-SIZED parameter carries. The compiler resolves `usize` to the
    /// target's fixed-width spelling before any discharge lane sees it
    /// (`discharge_binding_ty_for_target`), so what arrives here is `u64` on a
    /// 64-bit target and the clause is ordinary. This is the crates-level half
    /// of the fix for the binder-table misuse that silently dropped every
    /// pointer-sized precondition.
    #[test]
    fn a_pointer_sized_precondition_carries_once_the_binder_is_resolved() {
        for (width, resolved) in [
            (TargetPointerWidth::W64, "u64"),
            (TargetPointerWidth::W32, "u32"),
            (TargetPointerWidth::W16, "u16"),
        ] {
            assert_eq!(discharge_binding_ty_for_target("usize", width), resolved);
            let params: &[(&str, &str)] = &[("n", resolved), ("m", resolved)];
            let built = elaborate_ensures_under_requires(
                "n <= n",
                params,
                "irrelevant_self",
                &FacetTable::new(),
                &[hyp(0, "m <= n", params)],
            )
            .unwrap_or_else(|e| panic!("a resolved `usize` binder at {resolved} carries: {e}"));
            assert_eq!(built.bound_count(), 1);
            assert_eq!(built.value_binders, vec!["n".to_string(), "m".to_string()]);
        }
        // The UNRESOLVED spelling is refused, which is why the compiler must
        // resolve it and must not hand this lane a bare `usize`.
        let params: &[(&str, &str)] = &[("n", "usize"), ("m", "usize")];
        elaborate_ensures_under_requires(
            "n <= n",
            params,
            "irrelevant_self",
            &FacetTable::new(),
            &[hyp(0, "m <= n", params)],
        )
        .expect_err("a bare `usize` binder does not say which carrier it means");
    }

    // -----------------------------------------------------------------------
    // OR-A1 Inc 0 / Inc 1a — the lifted conclusion and `G1★`.
    // Predicted from the code and the r4 goal-string measurement; MEASURED
    // passing 2026-09-28 on `ora1-land` (all six).
    // -----------------------------------------------------------------------

    /// Inc 0: a LIFTED conclusion reaches the second rung only in `ProofLift`
    /// mode — the strict entry keeps refusing it byte for byte, so no existing
    /// caller changes.
    #[test]
    fn a_lifted_conclusion_reaches_the_second_rung_only_in_proof_lift_mode() {
        let params: &[(&str, &str)] = &[("a", "u64"), ("b", "u64")];
        let facets = FacetTable::new();
        let strict = elaborate_ensures_under_requires(
            "(b as nat) <= (a as nat)",
            params,
            "irrelevant_self",
            &facets,
            &[hyp(0, "b <= a", params)],
        );
        assert!(strict.is_err(), "a cast is `unsupported term shape` at Strict: {strict:?}");
        let lifted = elaborate_ensures_under_requires_in(
            "(b as nat) <= (a as nat)",
            params,
            "irrelevant_self",
            &facets,
            &[hyp(0, "b <= a", params)],
            &ProofClauseInputs::proof_lift(None),
        )
        .expect("the same clause builds a second rung in ProofLift mode");
        assert_eq!(lifted.bound_count(), 1);
        assert!(lifted.required_signed_lift_widths.is_empty(), "an unsigned lift seeds nothing");
    }

    /// H6: the signed widths BOTH goals name are returned as one union — here
    /// the conclusion names none and only the lifted hypothesis names `i64`.
    #[test]
    fn g1_star_reports_the_signed_widths_its_hypotheses_name() {
        let params: &[(&str, &str)] = &[("a", "i64"), ("b", "i64")];
        let built = elaborate_ensures_under_requires(
            "b <= a",
            params,
            "irrelevant_self",
            &FacetTable::new(),
            &[hyp(0, "b <= a", params)],
        )
        .expect("a signed precondition is carried");
        assert!(built.canonical_goal.is_some(), "{:?}", built.canonical_refusal);
        assert_eq!(
            built.required_signed_lift_widths,
            vec![MachineSIntWidth::I64],
            "`(b as int) <= (a as int)` names `trust_checked_toInt64`, so the holder of the \
             environment must seed it before grading G1★"
        );
        assert_ne!(
            built.canonical_goal.as_ref(),
            Some(&built.goal),
            "the signed order-key reading and the lifted `Int` reading are different terms"
        );
    }

    /// The lifted spelling of every `E-allow` shape, as text.
    #[test]
    fn the_lifted_spelling_of_each_e_allow_shape() {
        let params: &[(&str, &str)] =
            &[("a", "u64"), ("b", "u64"), ("x", "i32"), ("f", "bool")];
        let lift = |text: &str| {
            let ast: SynExpr = syn::parse_str(text).expect("parses");
            lift_hypothesis_source(&ast, params)
        };
        assert_eq!(lift("b <= a").as_deref(), Ok("(b as nat) <= (a as nat)"));
        assert_eq!(lift("(a) < (b)").as_deref(), Ok("(a as nat) < (b as nat)"));
        assert_eq!(lift("a == b").as_deref(), Ok("(a as nat) == (b as nat)"));
        assert_eq!(lift("a <= 1000u64").as_deref(), Ok("(a as nat) <= 1000"));
        assert_eq!(lift("x > 5").as_deref(), Ok("(x as int) > 5"));
        assert_eq!(lift("f").as_deref(), Ok("f"));
        // Every lifted spelling re-parses — `T_j` is elaborated from it.
        for text in ["!(a < b)", "(a <= b) || (b <= a)", "f == true", "a != b && x >= 0"] {
            let lifted = lift(text).unwrap_or_else(|e| panic!("`{text}`: {e}"));
            syn::parse_str::<SynExpr>(&lifted)
                .unwrap_or_else(|e| panic!("`{text}` lifts to `{lifted}`, which must parse: {e}"));
        }
        // Outside the fragment: refused, never approximated.
        for text in ["a + b > 10", "helper(a) == b", "a"] {
            assert!(lift(text).is_err(), "`{text}` has no lifted reading");
        }
    }

    /// `G1★` differs from `G1` ONLY in the hypothesis bodies: same binders, same
    /// bound set, same conclusion — structurally, not by string.
    #[test]
    fn g1_star_shares_g1s_binders_bound_set_and_conclusion() {
        let params: &[(&str, &str)] = &[("a", "u64"), ("b", "u64"), ("c", "u64")];
        let built = elaborate_ensures_under_requires(
            "a <= b",
            params,
            "irrelevant_self",
            &FacetTable::new(),
            &[
                hyp(0, "a == b", params),
                hyp(1, "a + c > 10", params),
                hyp(2, "c <= a", params),
            ],
        )
        .expect("two eligible clauses");
        let canonical = built.canonical_goal.as_ref().expect("G1★ builds on E-allow");
        let n = built.value_binders.len() + built.bound_count();
        assert_eq!(built.bound_count(), 2, "the arithmetic clause is omitted from BOTH goals");
        assert_eq!(
            peel_pis(canonical, n),
            peel_pis(&built.goal, n),
            "G1★'s conclusion must be G1's conclusion, byte for byte"
        );
        assert_eq!(
            built.hypotheses[0].lifted_text.as_deref(),
            Some("(a as nat) == (b as nat)")
        );
        assert_eq!(built.hypotheses[1].lifted_text, None, "an omitted row has no lifted reading");
        assert_eq!(built.hypotheses[2].lifted_text.as_deref(), Some("(c as nat) <= (a as nat)"));
        assert_ne!(
            canonical, &built.goal,
            "`Eq UInt64 a b` and `Eq Nat (toNat a) (toNat b)` are different hypotheses"
        );
    }

    /// Binder-order control for `G1★` — the off-by-one the kernel cannot catch
    /// between two same-carrier binders. Swapping the operands of the carried
    /// hypothesis must change the goal.
    #[test]
    fn g1_star_hypotheses_bind_the_authored_parameters() {
        let params: &[(&str, &str)] = &[("a", "u64"), ("b", "u64")];
        let build = |text: &str| {
            elaborate_ensures_under_requires(
                "a <= a",
                params,
                "irrelevant_self",
                &FacetTable::new(),
                &[hyp(0, text, params)],
            )
            .expect("builds")
            .canonical_goal
            .expect("G1★ builds")
        };
        assert_ne!(build("b <= a"), build("a <= b"), "swapped binders must not collapse");
        assert_eq!(build("b <= a"), build("(b) <= (a)"), "parentheses are not a reading");
    }

    /// A carrier the lift table has no row for (`usize64`, the statement-only
    /// pointer-sized spelling) still gets `G1` — and `G1★` is refused with a
    /// reason, never approximated. The compiler never hands this lane that
    /// spelling (it resolves `usize` to `u64` first), which is exactly why the
    /// refusal is a disclosure rather than a lost capability.
    #[test]
    fn g1_star_is_refused_not_approximated_where_the_lift_table_has_no_row() {
        let params: &[(&str, &str)] = &[("n", "usize64"), ("m", "usize64")];
        let built = elaborate_ensures_under_requires(
            "n <= n",
            params,
            "irrelevant_self",
            &FacetTable::new(),
            &[hyp(0, "m <= n", params)],
        )
        .expect("G1 builds over the fixed-width pointer carrier");
        assert!(built.canonical_goal.is_none(), "no lift row, no G1★");
        assert!(
            built.canonical_refusal.as_deref().is_some_and(|r| r.contains("`requires` #0")),
            "the refusal names the clause: {:?}",
            built.canonical_refusal
        );
        assert!(built.hypotheses[0].lifted_text.is_none());
    }
}

/// The FORWARDING mint (joint Rust+Lean cited lane, 2026-09-15): the kernel is
/// the sole judge of the minted equation, and the argument map is the call's,
/// not the signature's.
#[cfg(test)]
mod forwarding_mint_tests {
    use clean_kernel::{Environment, Expr, Name, TypeChecker};

    use super::{
        Domain, FacetTable, MachineUIntWidth, admit_expr_function, admit_forwarding_function,
        admit_projection_function, elaborate_ensures, elaborate_ensures_with_domains,
        elaborate_goal_typed_with_facets,
    };

    fn u64() -> Domain {
        Domain::Machine(MachineUIntWidth::U64)
    }

    fn u32() -> Domain {
        Domain::Machine(MachineUIntWidth::U32)
    }

    #[test]
    fn forwarding_mint_applies_the_callee_in_the_calls_argument_order() {
        let mut env = Environment::with_prelude();
        // A two-parameter callee that returns its FIRST argument.
        admit_projection_function(&mut env, "callee_fst", &[u64(), u64()], 0).expect("callee");
        // `fn fwd(a, b) { callee_fst(b, a) }` — the argument map is `[1, 0]`.
        let admission =
            admit_forwarding_function(&mut env, "fwd_swapped", &[u64(), u64()], "callee_fst", &[1, 0], &u64())
                .expect("forwarding mint");
        assert_eq!(admission.arity, 2);
        assert_eq!(admission.kernel_const, "fwd_swapped");
        // Kernel-judged consequence: `fwd_swapped a b ≡ b` (the callee's first
        // argument is `b`), and NOT `≡ a` — a positional guess would have said `a`.
        let a = Expr::const_(Name::from_string("a_free"), vec![]);
        let b = Expr::const_(Name::from_string("b_free"), vec![]);
        // Free constants stand in for neutral variables: declare them as opaque
        // UInt64 axioms so the terms are closed and typeable.
        for (name, _) in [("a_free", &a), ("b_free", &b)] {
            env.add_decl(clean_kernel::Declaration::Axiom {
                name: Name::from_string(name),
                level_params: vec![],
                type_: u64().ty(),
            })
            .expect("opaque UInt64 constant");
        }
        let applied = Expr::apps(Expr::const_(Name::from_string("fwd_swapped"), vec![]), [a.clone(), b.clone()]);
        let tc = TypeChecker::new(&env);
        assert!(tc.is_def_eq(&applied, &b), "fwd_swapped a b must reduce to b");
        assert!(!tc.is_def_eq(&applied, &a), "fwd_swapped a b must NOT reduce to a");
    }

    #[test]
    fn forwarding_mint_fails_closed_on_every_shape_it_does_not_own() {
        let mut env = Environment::with_prelude();
        admit_projection_function(&mut env, "callee_u64", &[u64(), u64()], 0).expect("callee");
        // Out-of-range source parameter.
        assert!(
            admit_forwarding_function(&mut env, "f1", &[u64(), u64()], "callee_u64", &[0, 2], &u64())
                .is_err()
        );
        // Carrier mismatch: `u32` parameters forwarded into `UInt64` slots — the
        // kernel refuses the equation, so no admission is minted.
        assert!(
            admit_forwarding_function(&mut env, "f2", &[u32(), u32()], "callee_u64", &[0, 1], &u32())
                .is_err()
        );
        // Return-carrier mismatch alone.
        assert!(
            admit_forwarding_function(&mut env, "f3", &[u64(), u64()], "callee_u64", &[0, 1], &u32())
                .is_err()
        );
        // Wrong arity for the callee.
        assert!(
            admit_forwarding_function(&mut env, "f4", &[u64(), u64()], "callee_u64", &[0], &u64())
                .is_err()
        );
        // An unregistered callee, an empty callee, and a self-forward.
        assert!(
            admit_forwarding_function(&mut env, "f5", &[u64()], "no_such_const", &[0], &u64()).is_err()
        );
        assert!(admit_forwarding_function(&mut env, "f6", &[u64()], "", &[0], &u64()).is_err());
        assert!(admit_forwarding_function(&mut env, "f7", &[u64()], "f7", &[0], &u64()).is_err());
        // None of the refusals left a constant behind.
        for name in ["f1", "f2", "f3", "f4", "f5", "f6", "f7"] {
            assert!(env.get_const(&Name::from_string(name)).is_none(), "{name} must not be registered");
        }
    }

    #[test]
    fn wave499_facet_table_arc_cow_and_ensures_ast_reuse_parity() {
        let mut env = Environment::with_prelude();
        let adm = admit_expr_function(&mut env, "inc_u64_def", "x + 1", &["x"], &u64())
            .expect("admit inc_u64");
        let mut facets =
            FacetTable::from_structural_facets([("inc_u64", true, true, true, true)]);
        facets.admit("inc_u64", adm);
        facets.set_shadowed_idents([("shadowed_param", "help text")]);

        // Clone shares backing Arc storage until mutated (copy-on-write).
        let mut cloned = facets.clone();
        assert!(std::sync::Arc::ptr_eq(&facets.records, &cloned.records));
        assert!(std::sync::Arc::ptr_eq(&facets.shadowed_idents, &cloned.shadowed_idents));
        cloned.remove("inc_u64");
        assert!(!std::sync::Arc::ptr_eq(&facets.records, &cloned.records));
        assert!(facets.admitted("inc_u64").is_some());
        assert!(cloned.admitted("inc_u64").is_none());

        // `elaborate_ensures` reuses the parsed AST without double-parsing and matches
        // the rewritten goal byte-for-byte.
        let goal_ensures =
            elaborate_ensures("result == x + 1", &[("x", "u64")], "inc_u64", &facets)
                .expect("elaborate_ensures");
        let goal_direct = elaborate_goal_typed_with_facets(
            "inc_u64(x) == x + 1",
            &[("x", "u64")],
            &facets,
        )
        .expect("elaborate_goal_typed_with_facets");
        assert_eq!(goal_ensures, goal_direct);

        let goal_domains = elaborate_ensures_with_domains(
            &env,
            "result == x + 1",
            &[("x", u64())],
            "inc_u64",
            &facets,
        )
        .expect("elaborate_ensures_with_domains");
        assert_eq!(goal_domains, goal_direct);
    }
}
