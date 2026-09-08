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

fn nat() -> Expr {
    Expr::const_(Name::from_string("Nat"), vec![])
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

fn kernel_nat_lit(n: u128) -> Expr {
    match u64::try_from(n) {
        Ok(n) => Expr::nat_lit(n),
        Err(_) => Expr::nat_lit_u128(n),
    }
}

fn bit_mask(bits: u32) -> u128 {
    if bits == 128 { u128::MAX } else { (1u128 << bits) - 1 }
}

fn signed_positive_max(bits: u32) -> u128 {
    (1u128 << (bits - 1)) - 1
}

fn signed_negative_magnitude_max(bits: u32) -> u128 {
    1u128 << (bits - 1)
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
            Domain::OptionSigned(_) => None,
            Domain::Signed(width) => Some(width.bits()),
            Domain::U128 => Some(128),
            Domain::USize(width) | Domain::ISize(width) => Some(width.bits()),
            Domain::Nat | Domain::Machine(_) | Domain::Bool => None,
        }
    }

    fn is_signed(&self) -> bool {
        matches!(self, Domain::Signed(_) | Domain::ISize(_))
    }

    fn rust_name(&self) -> &'static str {
        match self {
            Domain::OptionSigned(MachineSIntWidth::I8) => "Option<i8>",
            Domain::OptionSigned(MachineSIntWidth::I16) => "Option<i16>",
            Domain::OptionSigned(MachineSIntWidth::I32) => "Option<i32>",
            Domain::OptionSigned(MachineSIntWidth::I64) => "Option<i64>",
            Domain::OptionSigned(MachineSIntWidth::I128) => "Option<i128>",
            Domain::Nat => "nat",
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
            Expr::const_(Name::from_string("BitVec.toNat"), vec![]),
            [self.bitvec_width_expr()?, value],
        ))
    }

    fn bitvec_of_nat(&self, value: Expr) -> Result<Expr, String> {
        Ok(Expr::apps(
            Expr::const_(Name::from_string("BitVec.ofNat"), vec![]),
            [self.bitvec_width_expr()?, value],
        ))
    }

    fn bitvec_order_key(&self, value: Expr) -> Result<Expr, String> {
        let bits = self
            .bitvec_bits()
            .ok_or_else(|| format!("`{}` is not represented by a BitVec", self.rust_name()))?;
        let nat_value = self.bitvec_to_nat(value)?;
        if self.is_signed() {
            // Flipping the sign bit maps two's-complement signed order to
            // ordinary unsigned order, bijectively:
            //   MIN..-1 ↦ 0..2^(w-1)-1, 0..MAX ↦ 2^(w-1)..2^w-1.
            Ok(Expr::apps(
                Expr::const_(Name::from_string("Nat.xor"), vec![]),
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
            Domain::OptionSigned(_) => Err(format!(
                "`{}` has no runtime monitor carrier (Option results are \
                 kernel-goal-only)",
                self.rust_name()
            )),
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
            Domain::OptionSigned(width) => Expr::app(
                Expr::const_(Name::from_string("Option"), vec![Level::zero()]),
                Domain::Signed(*width).ty(),
            ),
            Domain::Nat => nat(),
            Domain::Machine(width) => Expr::const_(Name::from_string(width.carrier()), vec![]),
            Domain::Signed(_) | Domain::U128 | Domain::USize(_) | Domain::ISize(_) => Expr::app(
                Expr::const_(Name::from_string("BitVec"), vec![]),
                self.bitvec_width_expr().expect("closed BitVec domain"),
            ),
            Domain::Bool => Expr::const_(Name::from_string("Bool"), vec![]),
        }
    }

    /// The binary op constant name for `+` / `*`. Never called for
    /// [`Domain::Bool`] (arithmetic is gated in `elab_term`); the arm returns an
    /// unresolved sentinel so a missed gate fails as a kernel `UnknownConst`
    /// rather than silently or by panic.
    fn op(&self, which: &str) -> String {
        match self {
            Domain::OptionSigned(_) => "Option.__no_arithmetic__".to_string(),
            Domain::Nat => format!("Nat.{which}"),
            Domain::Machine(width) => format!("{}.{which}", width.carrier()),
            Domain::Signed(_) | Domain::U128 | Domain::USize(_) | Domain::ISize(_) => {
                format!("BitVec.__use_exact_{which}_encoding__")
            }
            Domain::Bool => "Bool.__no_arithmetic__".to_string(),
        }
    }

    fn arithmetic(&self, which: &str, lhs: Expr, rhs: Expr) -> Result<Expr, String> {
        match self {
            Domain::OptionSigned(_) => Err(format!(
                "arithmetic is not supported for `{}` (an Option carrier has \
                 constructors and equality only)",
                self.rust_name()
            )),
            Domain::Nat | Domain::Machine(_) => {
                let op = self.op(which);
                Ok(Expr::apps(Expr::const_(Name::from_string(&op), vec![]), [lhs, rhs]))
            }
            Domain::Signed(_) | Domain::U128 | Domain::USize(_) | Domain::ISize(_) => {
                let lhs = self.bitvec_to_nat(lhs)?;
                let rhs = self.bitvec_to_nat(rhs)?;
                let nat_value = match which {
                    "add" | "mul" => Expr::apps(
                        Expr::const_(Name::from_string(&format!("Nat.{which}")), vec![]),
                        [lhs, rhs],
                    ),
                    "sub" => {
                        // `(a + 2^w) - b` is non-negative for in-range a,b and
                        // is congruent to `a-b (mod 2^w)`.  Re-embedding via
                        // `BitVec.ofNat` therefore gives exact wrapping
                        // subtraction without relying on an unseeded BitVec op.
                        let bits = self.bitvec_bits().expect("closed BitVec domain");
                        let modulus = Expr::apps(
                            Expr::const_(Name::from_string("Nat.pow"), vec![]),
                            [Expr::nat_lit(2), Expr::nat_lit(u64::from(bits))],
                        );
                        let biased = Expr::apps(
                            Expr::const_(Name::from_string("Nat.add"), vec![]),
                            [lhs, modulus],
                        );
                        Expr::apps(
                            Expr::const_(Name::from_string("Nat.sub"), vec![]),
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
        match self {
            Domain::OptionSigned(_) => nat_pred("Option.__no_ordering__", a, b),
            Domain::Nat => nat_pred(&format!("Nat.{name}"), a, b),
            Domain::Machine(width) => {
                let carrier = width.carrier();
                let to_nat = Expr::const_(Name::from_string(&format!("{carrier}.toNat")), vec![]);
                let an = Expr::app(to_nat.clone(), a);
                let bn = Expr::app(to_nat, b);
                nat_pred(&format!("Nat.{name}"), an, bn)
            }
            Domain::Signed(_) | Domain::U128 | Domain::USize(_) | Domain::ISize(_) => {
                match (self.bitvec_order_key(a), self.bitvec_order_key(b)) {
                    (Ok(an), Ok(bn)) => nat_pred(&format!("Nat.{name}"), an, bn),
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
                    Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
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
            Domain::OptionSigned(_) => {
                Expr::const_(Name::from_string("Option.__no_zero__"), vec![])
            }
            Domain::Nat => Expr::const_(Name::from_string("Nat.zero"), vec![]),
            Domain::Machine(width) => {
                let carrier = width.carrier();
                Expr::app(
                    Expr::const_(Name::from_string(&format!("{carrier}.ofNat")), vec![]),
                    Expr::const_(Name::from_string("Nat.zero"), vec![]),
                )
            }
            Domain::Signed(_) | Domain::U128 | Domain::USize(_) | Domain::ISize(_) => self
                .bitvec_of_nat(Expr::const_(Name::from_string("Nat.zero"), vec![]))
                .expect("closed BitVec domain"),
            Domain::Bool => Expr::const_(Name::from_string("Bool.__no_zero__"), vec![]),
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
            Domain::OptionSigned(_) => Err(format!(
                "an integer literal is not a `{}` (write `Some(<literal>)` or \
                 `None`)",
                self.rust_name()
            )),
            Domain::Nat => Ok(kernel_nat_lit(n)),
            Domain::Machine(width) => {
                if n > width.max_value() {
                    return Err(format!(
                        "literal {n} is out of range for `{}` (max {})",
                        width.rust_name(),
                        width.max_value()
                    ));
                }
                let carrier = width.carrier();
                Ok(Expr::app(
                    Expr::const_(Name::from_string(&format!("{carrier}.ofNat")), vec![]),
                    kernel_nat_lit(n),
                ))
            }
            Domain::Signed(_) | Domain::ISize(_) => {
                let bits = self.bitvec_bits().expect("closed BitVec domain");
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
                let bits = self.bitvec_bits().expect("closed BitVec domain");
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
        if !self.is_signed() {
            return Err(format!("a negative literal is not supported for `{}`", self.rust_name()));
        }
        let bits = self.bitvec_bits().expect("closed signed BitVec domain");
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
                Name::from_string(if b { "Bool.true" } else { "Bool.false" }),
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
            Domain::Nat | Domain::Bool => None,
            // No shifts on an Option carrier.
            Domain::OptionSigned(_) => None,
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
            | Domain::Machine(_)
            | Domain::Signed(_)
            | Domain::U128
            | Domain::USize(_)
            | Domain::ISize(_)
            | Domain::OptionSigned(_) => false,
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
            Domain::Nat => Carrier::Nat,
            Domain::Machine(width) => Carrier::UInt(*width),
            Domain::Signed(_) | Domain::U128 | Domain::USize(_) | Domain::ISize(_) => {
                Carrier::BitVec(self.bitvec_bits().expect("closed BitVec domain"))
            }
            Domain::Bool => Carrier::Bool,
            Domain::OptionSigned(width) => {
                Carrier::Option(Box::new(Domain::Signed(*width).carrier()))
            }
        }
    }
}

/// Collect free variable identifiers in order of first appearance.
fn collect_vars(e: &SynExpr, out: &mut Vec<String>) {
    match e {
        SynExpr::Paren(p) => collect_vars(&p.expr, out),
        SynExpr::Binary(b) => {
            collect_vars(&b.left, out);
            collect_vars(&b.right, out);
        }
        SynExpr::Unary(u) => collect_vars(&u.expr, out),
        SynExpr::Path(p) => {
            if let Some(id) = p.path.get_ident() {
                let s = id.to_string();
                // `None` is the Option constructor LITERAL, never a clause
                // variable: Rust itself refuses a binding named `None`
                // (E0530, unit-variant shadowing), so no parameter row can
                // ever exist for it — collecting it would only poison the
                // exact-binding gate with a bogus free variable.
                if s != "None" && !out.contains(&s) {
                    out.push(s);
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
            let id = p
                .path
                .get_ident()
                .ok_or_else(|| "only bare identifiers are supported".to_string())?
                .to_string();
            // `None` is the Option CONSTRUCTOR literal, never a clause
            // variable (Rust refuses a binding named `None` — E0530), typed
            // exactly at an Option carrier: `Option.none.{0} (BitVec N)`.
            if id == "None" {
                if let Domain::OptionSigned(width) = dom {
                    return Ok(Expr::app(
                        Expr::const_(Name::from_string("Option.none"), vec![Level::zero()]),
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
            if let Some(pos) = vars.iter().position(|v| *v == id) {
                return Ok(Expr::bvar((vars.len() - 1 - pos) as u32 + offset));
            }
            // E6 bare citation (e6 probe f04's spelling): an admitted
            // ZERO-ARITY constant referenced with NO argument list elaborates
            // to its kernel constant — the same admission, the same I3
            // firewall, and the same constant the call arm resolves for
            // `id()`; only the surface spelling differs. A parametered
            // admission must be applied: its bare name is a function value,
            // which the term fragment does not speak, so it keeps failing
            // closed — with the fix named (v7/D3).
            if let Some(admission) = ambient_admission(&id) {
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
            Ok(Expr::bvar((vars.len() - 1 - pos) as u32 + offset))
        }
        SynExpr::Lit(l) => match &l.lit {
            Lit::Int(i) => {
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
            if !dom.is_signed() {
                return Err(format!(
                    "unary negation is only supported for a signed machine binding, not `{}`",
                    dom.rust_name()
                ));
            }
            if let Some(magnitude) = nonneg_int_literal(&u.expr) {
                return dom.negative_numeral(magnitude);
            }
            let value = elab_term(&u.expr, vars, offset, var_domains, dom)?;
            dom.arithmetic("sub", dom.zero(), value)
        }
        SynExpr::Binary(b) => {
            // `bool` has no arithmetic — `+ - * / %` over a boolean binding
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
                    Expr::app(Expr::app(Expr::const_(Name::from_string(nat_op), vec![]), a), b)
                };
                let dividend = elab_term(&b.left, vars, offset, var_domains, dom)?;
                let divisor = kernel_nat_lit(c);
                return Ok(match dom {
                    Domain::Nat => nat_bin(dividend, divisor),
                    Domain::Machine(width) => {
                        let carrier = width.carrier();
                        let to_nat =
                            Expr::const_(Name::from_string(&format!("{carrier}.toNat")), vec![]);
                        let of_nat =
                            Expr::const_(Name::from_string(&format!("{carrier}.ofNat")), vec![]);
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
                    // Unreachable: bool arithmetic is rejected at the top of this
                    // arm. Fail closed rather than panic if a gate is ever missed.
                    Domain::Bool => return Err("arithmetic is not supported for `bool`".into()),
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
                                Expr::const_(Name::from_string("Nat.mul"), vec![]),
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
                                Expr::app(Expr::const_(Name::from_string("Nat.div"), vec![]), a),
                                b,
                            )
                        };
                        match dom {
                            Domain::Nat => nat_div(l, divisor),
                            Domain::Machine(width) => {
                                let carrier = width.carrier();
                                let to_nat = Expr::const_(
                                    Name::from_string(&format!("{carrier}.toNat")),
                                    vec![],
                                );
                                let of_nat = Expr::const_(
                                    Name::from_string(&format!("{carrier}.ofNat")),
                                    vec![],
                                );
                                Expr::app(of_nat, nat_div(Expr::app(to_nat, l), divisor))
                            }
                            Domain::U128 | Domain::USize(_) => {
                                let value = nat_div(dom.bitvec_to_nat(l)?, divisor);
                                dom.bitvec_of_nat(value)?
                            }
                            Domain::Signed(_) | Domain::ISize(_) => {
                                return Err("signed right shift is not implemented".into());
                            }
                            Domain::Bool => {
                                return Err("bit-shift is not supported for `bool`".into());
                            }
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
                    Expr::app(Expr::app(Expr::const_(Name::from_string(nat_op), vec![]), a), b)
                };
                let l = elab_term(&b.left, vars, offset, var_domains, dom)?;
                let r = elab_term(&b.right, vars, offset, var_domains, dom)?;
                return Ok(match dom {
                    Domain::Nat => nat_bin(l, r),
                    Domain::Machine(width) => {
                        let carrier = width.carrier();
                        let to_nat =
                            Expr::const_(Name::from_string(&format!("{carrier}.toNat")), vec![]);
                        let of_nat =
                            Expr::const_(Name::from_string(&format!("{carrier}.ofNat")), vec![]);
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
                    let [inner] = c.args.iter().collect::<Vec<_>>()[..] else {
                        return Err("`Some(..)` takes exactly one argument".to_string());
                    };
                    let payload_dom = Domain::Signed(*width);
                    let payload = elab_term(inner, vars, offset, var_domains, &payload_dom)?;
                    return Ok(Expr::apps(
                        Expr::const_(Name::from_string("Option.some"), vec![Level::zero()]),
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
            if let Some(admission) = ambient_admission(&callee) {
                // I3: the use-site capability is decided BEFORE arity —
                // whether a use site may name the symbol at all is a prior
                // question to whether it applied the right number of
                // arguments, and answering them in the other order tells an
                // author to fix an arity in a call they were never allowed to
                // write. A PROOF use site never fails here.
                if let Err(refusal) = admission.require_at(ambient_use_site(), &callee) {
                    return Err(refusal.to_string());
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
                            let arg_dom = argument_domain(arg, c, var_domains, dom)?;
                            let declared = &carriers.params[i];
                            if arg_dom.carrier() != *declared {
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
    let var_domains = &uniform;
    match ast {
        SynExpr::Paren(p) => elaborate_prop(&p.expr, vars, offset, dom),
        // Logical connectives: operands are *propositions* — recurse.
        SynExpr::Unary(u) if matches!(u.op, syn::UnOp::Not(_)) => Ok(Expr::app(
            Expr::const_(Name::from_string("Not"), vec![]),
            elaborate_prop(&u.expr, vars, offset, dom)?,
        )),
        SynExpr::Binary(b) if matches!(b.op, BinOp::And(_)) => Ok(connective(
            "And",
            elaborate_prop(&b.left, vars, offset, dom)?,
            elaborate_prop(&b.right, vars, offset, dom)?,
        )),
        SynExpr::Binary(b) if matches!(b.op, BinOp::Or(_)) => Ok(connective(
            "Or",
            elaborate_prop(&b.left, vars, offset, dom)?,
            elaborate_prop(&b.right, vars, offset, dom)?,
        )),
        // Disequality `a != b` desugars to `!(a == b)` (see `ne_as_not_eq`).
        SynExpr::Binary(b) if matches!(b.op, BinOp::Ne(_)) => {
            elaborate_prop(&ne_as_not_eq(b), vars, offset, dom)
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
            Ok(Expr::const_(Name::from_string(if value { "True" } else { "False" }), vec![]))
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
    Expr::app(Expr::app(Expr::const_(Name::from_string(name), vec![]), a), b)
}

/// `And p q` / `Or p q` — the propositional connectives (`Prop → Prop → Prop`).
fn connective(name: &str, p: Expr, q: Expr) -> Expr {
    Expr::app(Expr::app(Expr::const_(Name::from_string(name), vec![]), p), q)
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
    let (ast, vars, var_domains) = parse_exact_typed_clause(spec, var_types)?;
    let body = elaborate_prop_multi(&ast, &vars, 0, &var_domains)?;
    close_over_multi(&vars, body, &var_domains)
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
fn strip_outer_parens(s: &str) -> &str {
    let mut t = s.trim();
    loop {
        let Some(inner) = t.strip_prefix('(').and_then(|r| r.strip_suffix(')')) else {
            return t;
        };
        // The stripped pair is matched iff depth never returns to zero inside.
        let mut depth = 1i32;
        let mut matched = true;
        for c in inner.chars() {
            match c {
                '(' => depth += 1,
                ')' => {
                    depth -= 1;
                    if depth == 0 {
                        matched = false;
                        break;
                    }
                }
                _ => {}
            }
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
fn split_top_level_implies(s: &str) -> Option<(&str, &str)> {
    let bytes = s.as_bytes();
    let mut depth = 0i32;
    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            b'(' => depth += 1,
            b')' => depth -= 1,
            b'=' if depth == 0 && bytes[i..].starts_with(b"==>") => {
                return Some((&s[..i], &s[i + 3..]));
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
    let (var, after) = rest.split_at(ident_end);
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
    let Some(comma) = after.find(',') else {
        return Err(format!("`{kw} {var}: …` expects `, <body>` after the binder type"));
    };
    let ty = after[..comma].trim();
    if ty.is_empty() {
        return Err(format!("`{kw} {var}:` is missing the binder type"));
    }
    let body_src = &after[comma + 1..];
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
fn body_has_top_level_colon(s: &str) -> bool {
    let bytes = s.as_bytes();
    let mut depth = 0i32;
    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            b'(' => depth += 1,
            b')' => depth -= 1,
            b':' if depth == 0 => {
                if i + 1 < bytes.len() && bytes[i + 1] == b':' {
                    i += 1; // skip `::`
                } else {
                    return true;
                }
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
            let r = elab_qclause(rhs, vars, offset + 1, var_domains)?;
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
                        Expr::const_(Name::from_string("Exists"), vec![Level::succ(Level::zero())]),
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
    let mut free = Vec::new();
    collect_qclause_free_vars(&clause, &mut Vec::new(), &mut free);
    let bindings = exact_typed_bindings(&free, var_types)?;
    let mut vars = free.clone();
    let mut var_domains = bindings;
    let body = elab_qclause(&clause, &mut vars, 0, &mut var_domains)?;
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
    /// admitter reads it off the kernel type's codomain). This is elaboration
    /// STEERING, never authority: [`atom_domain`] uses it to type a
    /// VARIABLE-FREE atom (`answer() == c42(0)`) at the callee's machine
    /// domain instead of the `Nat` default, and a wrongly recorded domain can
    /// only produce an ill-typed proposition the kernel then rejects — it can
    /// never make a false claim check. Private like the other
    /// evidence-bearing fields; the minting caller attaches it through
    /// [`Admission::with_return_domain`], and an absent domain simply leaves
    /// the pre-existing fail-closed default in force.
    return_domain: Option<Domain>,
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
        }
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

/// Facet records keyed by the callee path exactly as spelled in the spec
/// (e.g. `min` or `cmp::min`). Method calls are NOT keyed here yet: method
/// resolution is receiver-type-dependent, so their keying arrives with the
/// compiler-side wiring that has typeck results in hand; until then method
/// calls keep the unconditional fail-closed diagnostic.
#[derive(Debug, Clone, Default)]
pub struct FacetTable {
    map: std::collections::BTreeMap<String, FnFacets>,
    /// E6 brick 4: the kernel constant each admitted function was minted as,
    /// keyed by the same callee path as `map`. Populated ONLY by the
    /// kernel-import step; empty until then, so admission never fires.
    admissions: std::collections::BTreeMap<String, Admission>,
}

impl FacetTable {
    pub fn new() -> Self {
        Self::default()
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
        self.map.insert(callee_path.into(), facets);
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
        for (path, total, no_panic, pure, deterministic) in entries {
            let path = path.into();
            if let Some(existing) = self.map.get(&path) {
                let upgraded = FnFacets {
                    pure: promote(&existing.pure, pure),
                    total: promote(&existing.total, total),
                    deterministic: promote(&existing.deterministic, deterministic),
                    no_panic: promote(&existing.no_panic, no_panic),
                };
                self.map.insert(path, upgraded);
            }
        }
    }

    /// Remove a record (e.g. a bare-name key evicted as ambiguous). A missing
    /// key is fine — eviction must be idempotent. Also drops any admission for
    /// that key, so an evicted (ambiguous) name can never stay admitted.
    pub fn remove(&mut self, callee_path: &str) {
        self.map.remove(callee_path);
        self.admissions.remove(callee_path);
    }

    pub fn get(&self, callee_path: &str) -> Option<&FnFacets> {
        self.map.get(callee_path)
    }

    /// Record that `callee_path` has been ADMITTED as a Clean kernel constant
    /// (E6 brick 4). The caller is the kernel-import step, which mints the
    /// `Admission` only after the facets are certified and the kernel
    /// re-checks the definition. Recording it does NOT itself grant authority
    /// — [`Self::admitted`] still gates on [`FnFacets::admissible`].
    pub fn admit(&mut self, callee_path: impl Into<String>, admission: Admission) {
        self.admissions.insert(callee_path.into(), admission);
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
    pub fn admitted(&self, callee_path: &str) -> Option<&Admission> {
        let certified = self.map.get(callee_path).is_some_and(FnFacets::admissible);
        if certified { self.admissions.get(callee_path) } else { None }
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
        self.admissions
            .values()
            .find(|admission| admission.kernel_const == kernel_const)
            .map(Admission::status)
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
        self.admissions.contains_key(callee_path)
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
        | Domain::U128
        | Domain::USize(_)
        | Domain::ISize(_)
        | Domain::Bool
        // The select mint's `ite` encoding has no reading over an Option
        // carrier (no order, no decidable comparison): fail closed.
        | Domain::OptionSigned(_) => false,
    };
    // Both the compared pair and the branch pair must be carriers the `ite`
    // encoding is faithful for; an unrelated binder's carrier is irrelevant.
    if !carrier_ok(d) || !carrier_ok(cmp_domain) {
        return Err("select currently requires a machine-integer or signed-integer domain".into());
    }
    // Under n binders the source parameter i is de Bruijn index n-1-i.
    let bvar = |i: usize| Expr::bvar((n - 1 - i) as u32);
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
    let (l, r) = (bvar(cmp_left), bvar(cmp_right)); // carrier level — NOT .toNat
    let (prop, inst) = decidable_comparison(cmp_domain, cmp, l, r)?;
    // ARGUMENT ORDER: `ite α c h t e` takes THEN fourth and ELSE fifth, the
    // opposite of `Bool.rec`, which took ELSE first. Reversing these silently
    // mints `max` where the program wrote `min`, and the E9 goal still closes
    // whenever the island happens to be reversed the same way — so a positive
    // fixture alone does NOT catch it. The paired NEG probe is the net.
    let body = Expr::apps(
        Expr::const_(Name::from_string("ite"), vec![one]),
        [ty.clone(), prop, inst, bvar(then_param), bvar(else_param)],
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
    let carrier = match d {
        Domain::Machine(w) => w.carrier(),
        _ => return Err("select currently requires a machine-integer domain".into()),
    };
    // Under n binders the source parameter i is de Bruijn index n-1-i.
    let bvar = |i: usize| Expr::bvar((n - 1 - i) as u32);
    let ty = d.ty();
    let zero = Level::zero();
    let one = Level::succ(Level::zero());
    // The comparison's operands: the parameter on the LEFT, the range-checked
    // numeral on the RIGHT. `Domain::numeral` fails closed on an out-of-range
    // literal BEFORE the kernel, exactly as in `admit_constant_function`.
    let (l, r) = (bvar(cmp_param), d.numeral(literal)?);
    let inst_c = |s: &str| Expr::const_(Name::from_string(s), vec![]);
    let (prop, inst) = match cmp {
        SelectCmp::Lt => (
            Expr::apps(
                Expr::const_(Name::from_string("LT.lt"), vec![zero.clone()]),
                [ty.clone(), inst_c(&format!("instLT{carrier}")), l.clone(), r.clone()],
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
                                Expr::proj(Name::from_string(carrier), 0, bvar(cmp_param)),
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
                [ty.clone(), inst_c(&format!("instLE{carrier}")), l.clone(), r.clone()],
            ),
            Expr::apps(inst_c(&format!("instDecidable{carrier}Le")), [l, r]),
        ),
        SelectCmp::Eq => (
            Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![one.clone()]),
                [ty.clone(), l.clone(), r.clone()],
            ),
            Expr::apps(inst_c(&format!("instDecidableEq{carrier}")), [l, r]),
        ),
    };
    // ARGUMENT ORDER: `ite α c h t e` takes THEN fourth and ELSE fifth — the
    // same polarity trap `admit_select_function` documents; the paired
    // mutation probes are the net here too.
    let body = Expr::apps(
        Expr::const_(Name::from_string("ite"), vec![one]),
        [ty.clone(), prop, inst, bvar(then_param), bvar(else_param)],
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
    let mut indices = vec![cmp_left];
    for operand in [cmp_right, then_arm, else_arm] {
        if let SelectOperand::Param(index) = operand {
            indices.push(index);
        }
    }
    for index in indices {
        if index >= n {
            return Err(format!("select index {index} out of range for a {n}-parameter function"));
        }
    }
    let d = param_domains.first().ok_or("select needs at least one parameter")?;
    if !param_domains.iter().all(|x| x == d) {
        return Err("select over mixed parameter domains is unsupported".into());
    }
    let carrier = match d {
        Domain::Machine(w) => w.carrier(),
        _ => return Err("select currently requires a machine-integer domain".into()),
    };
    // Under n binders the source parameter i is de Bruijn index n-1-i.
    let bvar = |i: usize| Expr::bvar((n - 1 - i) as u32);
    // ONE operand renderer for every position — the comparison's right-hand
    // side and both arms. A numeral is minted by `Domain::numeral`, which
    // range-checks it and fails closed before the kernel; that is also the
    // spelling (`{C}.ofNat v`) the real island elaborates a constant arm to.
    let operand = |o: SelectOperand| -> Result<Expr, String> {
        match o {
            SelectOperand::Param(index) => Ok(bvar(index)),
            SelectOperand::Literal(value) => d.numeral(value),
        }
    };
    let ty = d.ty();
    let zero = Level::zero();
    let one = Level::succ(Level::zero());
    let l = bvar(cmp_left);
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
                [ty.clone(), inst_c(&format!("instLT{carrier}")), l.clone(), r.clone()],
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
                                Expr::proj(Name::from_string(carrier), 0, bvar(cmp_left)),
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
                [ty.clone(), inst_c(&format!("instLT{carrier}")), l.clone(), r.clone()],
            ),
            Expr::apps(inst_c(&format!("instDecidable{carrier}Lt")), [l, r]),
        ),
        (SelectCmp::Le, _) => (
            Expr::apps(
                Expr::const_(Name::from_string("LE.le"), vec![zero.clone()]),
                [ty.clone(), inst_c(&format!("instLE{carrier}")), l.clone(), r.clone()],
            ),
            Expr::apps(inst_c(&format!("instDecidable{carrier}Le")), [l, r]),
        ),
        (SelectCmp::Eq, _) => (
            Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![one.clone()]),
                [ty.clone(), l.clone(), r.clone()],
            ),
            Expr::apps(inst_c(&format!("instDecidableEq{carrier}")), [l, r]),
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
    let mut indices = vec![cmp_left];
    for operand in [cmp_right, then_arm, else_arm] {
        if let SelectOperand::Param(index) = operand {
            indices.push(index);
        }
    }
    for index in indices {
        if index >= n {
            return Err(format!("select index {index} out of range for a {n}-parameter function"));
        }
    }
    let d = param_domains.first().ok_or("select needs at least one parameter")?;
    if !param_domains.iter().all(|x| x == d) {
        return Err("select over mixed parameter domains is unsupported".into());
    }
    let carrier = match d {
        Domain::Machine(w) => w.carrier(),
        _ => return Err("select currently requires a machine-integer domain".into()),
    };
    // Under n binders the source parameter i is de Bruijn index n-1-i.
    let bvar = |i: usize| Expr::bvar((n - 1 - i) as u32);
    // ONE operand renderer for every position, exactly as the general select
    // route states it: a numeral is minted by `Domain::numeral`, which
    // range-checks it and fails closed before the kernel, and which is the
    // spelling (`{C}.ofNat v`) the real island elaborates a constant operand
    // to in this tree as well (measured, `l5_p1`).
    let operand = |o: SelectOperand| -> Result<Expr, String> {
        match o {
            SelectOperand::Param(index) => Ok(bvar(index)),
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
                [ty.clone(), inst_c(&format!("instDecidableEq{carrier}"))],
            ),
            bvar(cmp_left),
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
    let mut indices = Vec::new();
    for operand in [cmp_left, cmp_right] {
        if let SelectBeqOperand::Param(index) = operand {
            indices.push(*index);
        }
    }
    for operand in [then_arm, else_arm] {
        if let SelectOperand::Param(index) = operand {
            indices.push(index);
        }
    }
    for index in indices {
        if index >= n {
            return Err(format!("select index {index} out of range for a {n}-parameter function"));
        }
    }
    let d = param_domains.first().ok_or("select needs at least one parameter")?;
    if !param_domains.iter().all(|x| x == d) {
        return Err("select over mixed parameter domains is unsupported".into());
    }
    let carrier = match d {
        Domain::Machine(w) => w.carrier(),
        _ => return Err("select currently requires a machine-integer domain".into()),
    };
    // Under n binders the source parameter i is de Bruijn index n-1-i — the
    // convention `elab_term` uses at offset 0, so a computed operand's term
    // needs no re-indexing and there is no second place an index could be set.
    let bvar = |i: usize| Expr::bvar((n - 1 - i) as u32);
    let names: Vec<String> = (0..n).map(|i| format!("p{i}")).collect();
    let arm = |o: SelectOperand| -> Result<Expr, String> {
        match o {
            SelectOperand::Param(index) => Ok(bvar(index)),
            SelectOperand::Literal(value) => d.numeral(value),
        }
    };
    let decision_operand = |o: &SelectBeqOperand| -> Result<Expr, String> {
        match o {
            SelectBeqOperand::Param(index) => Ok(bvar(*index)),
            SelectBeqOperand::Literal(value) => d.numeral(*value),
            SelectBeqOperand::Computed(rendering) => {
                let syn: SynExpr = syn::parse_str(rendering)
                    .map_err(|e| format!("parse error in a computed select operand: {e}"))?;
                elab_term(&syn, &names, 0, &uniform_var_domains(&names, d), d)
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
                [ty.clone(), inst_c(&format!("instDecidableEq{carrier}"))],
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
fn ambient_admission(callee: &str) -> Option<Admission> {
    ADMISSION_FACETS
        .with(|slot| slot.borrow().as_ref().and_then(|table| table.admitted(callee).cloned()))
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
    // E3: a quantified clause is not syn-parseable as a whole, so the facet
    // diagnostic walk runs over the pre-parsed leaves instead; the admission
    // scope then covers the same quantified elaboration path.
    if clause_uses_quantifier_fragment(spec) {
        let clause = parse_qclause(spec, true)?;
        if let Some(err) = qclause_first_call_facet_error(&clause, facets) {
            return Err(err);
        }
        let _scope = AdmissionScope::enter_at(facets.clone(), use_site);
        return elaborate_goal_typed(spec, var_types);
    }
    let ast: SynExpr = syn::parse_str(spec).map_err(|e| format!("parse error: {e}"))?;
    if let Some(err) = first_call_facet_error(&ast, facets) {
        return Err(err);
    }
    let _scope = AdmissionScope::enter_at(facets.clone(), use_site);
    elaborate_goal_typed(spec, var_types)
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
    if self_fn_name.is_empty() {
        return Err("elaborate_ensures requires the specified function's name".to_string());
    }
    // A quantified/implication clause (E3 fragment) is not Rust-parseable by syn
    // and cannot carry the `result` substitution yet; route it straight to the
    // quantified elaborator over just the parameters it uses. `result` inside a
    // quantifier is a free variable there and stays fail-closed (a deeper slice).
    if clause_uses_quantifier_fragment(clause) {
        let used = discharge_used_bindings(clause, param_types);
        return elaborate_goal_typed_with_facets(clause, &used, facets);
    }
    let param_names: Vec<String> = param_types.iter().map(|(n, _)| (*n).to_string()).collect();
    let ast: SynExpr = syn::parse_str(clause).map_err(|e| format!("parse error: {e}"))?;
    // FIELD PROJECTIONS FIRST. A struct-returning body has no whole-function
    // import -- only one constant per field -- so the admission lookup below
    // would fail closed on a clause that never needed it. Rewriting
    // `result.<field>` here leaves the clause free of `result` whenever every
    // mention was a projection, and the ordinary path then elaborates it.
    let ast = rewrite_result_fields(&ast, self_fn_name, &param_names, facets)?;
    // The clause the rest of this function elaborates is the REWRITTEN one: a
    // field projection is gone, replaced by its per-field import call. Carrying
    // the original string past this point left `result.<field>` in the source
    // the binding gate reads, which reported it as a missing binding.
    let clause_owned = quote::quote!(#ast).to_string();
    let clause: &str = &clause_owned;
    // A clause that never mentions `result` is a ∀-params statement independent
    // of the function's return value — its proof covers the postcondition for
    // ANY body, so the SELF-admission gate is required only when `result` must
    // be substituted with the defining equation. (Calls inside the clause are
    // still individually gated on THEIR admissions by the elaborator.)
    if !mentions_result(&ast) {
        let used = discharge_used_bindings(clause, param_types);
        return elaborate_goal_typed_with_facets(clause, &used, facets);
    }
    let Some(admission) = facets.admitted(self_fn_name) else {
        // `result` has no kernel denotation unless the function is E6-admitted;
        // fail closed (design note §3 restriction), same as any un-admitted call.
        return Err(format!(
            "ensures discharge requires the specified function `{self_fn_name}` to be \
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
    if admission.param_names.as_ref().is_some_and(|minted| *minted != param_names) {
        let minted = admission.param_names.as_ref().expect("checked just above");
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
    let rewritten_src = quote::quote!(#rewritten).to_string();
    // Elaborate over the parameters only — `result` is gone, replaced by the
    // admitted self-call, which `elab_term` resolves to `self_fn_def(params)`.
    // Filter to the params the rewritten clause actually uses so a clause that
    // constrains only a SUBSET of the parameters (e.g. a quantified clause, or
    // `ensures result >= 0`) still binds exactly its free variables.
    let used = discharge_used_bindings(&rewritten_src, param_types);
    elaborate_goal_typed_with_facets(&rewritten_src, &used, facets)
}

/// For the ensures-discharge path, the subset of `param_types` whose names are
/// FREE variables of `clause` — a discharge goal over only the variables the
/// clause uses is sound (an unused parameter is simply not constrained), and it
/// keeps the exact-binding gate satisfiable for a clause that references fewer
/// than all the parameters (quantified clauses, constant bounds, single-param
/// predicates in a multi-param function). Routes quantified vs plain clauses the
/// same way `elaborate_goal_typed` does; on any parse failure it returns the
/// full list unchanged so the elaborator reports the real error.
fn discharge_used_bindings<'a>(
    clause: &str,
    param_types: &[(&'a str, &'a str)],
) -> Vec<(&'a str, &'a str)> {
    let free: std::collections::BTreeSet<String> = if clause_uses_quantifier_fragment(clause) {
        match parse_qclause(clause, true) {
            Ok(qc) => {
                let mut acc = Vec::new();
                collect_qclause_free_vars(&qc, &mut Vec::new(), &mut acc);
                acc.into_iter().collect()
            }
            Err(_) => return param_types.to_vec(),
        }
    } else {
        match syn::parse_str::<SynExpr>(clause) {
            Ok(ast) => {
                let mut acc = Vec::new();
                collect_vars(&ast, &mut acc);
                acc.into_iter().collect()
            }
            Err(_) => return param_types.to_vec(),
        }
    };
    param_types.iter().filter(|(n, _)| free.contains(*n)).copied().collect()
}

/// Whether a clause AST mentions the reserved `result` identifier anywhere a
/// clause VARIABLE can occur (same traversal as [`rewrite_result_to`]; a call's
/// callee path is a function identity, not a variable).
fn mentions_result(e: &SynExpr) -> bool {
    match e {
        SynExpr::Path(p) => p.path.is_ident("result"),
        SynExpr::Paren(p) => mentions_result(&p.expr),
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

/// Walk the spec AST; on the first program-function call, produce the
/// facet-aware E6 diagnostic. `None` means the spec contains no calls and
/// elaboration may proceed on the ordinary path.
fn first_call_facet_error(ast: &SynExpr, facets: &FacetTable) -> Option<String> {
    match ast {
        SynExpr::Paren(p) => first_call_facet_error(&p.expr, facets),
        SynExpr::Unary(u) => first_call_facet_error(&u.expr, facets),
        SynExpr::Binary(b) => first_call_facet_error(&b.left, facets)
            .or_else(|| first_call_facet_error(&b.right, facets)),
        SynExpr::Call(c) => {
            let callee = match &*c.func {
                SynExpr::Path(p) => p
                    .path
                    .segments
                    .iter()
                    .map(|s| s.ident.to_string())
                    .collect::<Vec<_>>()
                    .join("::"),
                _ => "<expression>".to_string(),
            };
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
                None => format!(
                    "no diagnostic E6 facet record exists for `{callee}`; public facet \
                     findings cannot admit a call and no sealed, item-bound kernel \
                     admission exists, so the program-function call fails closed; \
                     mention the function through its operational relation instead"
                ),
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

/// Parse a typed clause and resolve exactly the carrier shared by every free
/// identifier. This is the single binding gate used by both typed statement
/// elaboration and typed monitor construction, so the report-only monitor lane
/// cannot accept a looser name/type surface than the statement it certifies.
fn parse_exact_typed_clause(
    spec: &str,
    var_types: &[(&str, &str)],
) -> Result<(SynExpr, Vec<String>, BTreeMap<String, Domain>), String> {
    let ast: SynExpr = syn::parse_str(spec).map_err(|e| format!("parse error: {e}"))?;
    let mut vars = Vec::new();
    collect_vars(&ast, &mut vars);
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
    vars.retain(|v| var_types.iter().any(|(n, _)| n == v) || ambient_admission(v).is_none());
    let bindings = exact_typed_bindings(&vars, var_types)?;
    Ok((ast, vars, bindings))
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
    Ok(bindings)
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
fn atom_domain(atom: &SynExpr, var_domains: &BTreeMap<String, Domain>) -> Result<Domain, String> {
    let mixed = match resolved_atom_domain_all_vars(atom, var_domains) {
        Ok(Some(dom)) => return Ok(dom),
        Ok(None) => {
            // main's C6 lane: a variable-free atom derives its domain from
            // TERM EVIDENCE, and CONFLICTING evidence refuses -- which is why
            // the collector runs FIRST and the call-result steering is only a
            // fallback for an atom the collector finds no evidence in. An
            // early return on the call result alone silently swallowed a
            // u64-callee-vs-u32-literal conflict (measured:
            // conflicting_term_domain_evidence_refuses).
            let mut dom: Option<Domain> = None;
            collect_term_domain_evidence(atom, &mut dom)?;
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
                let callee = p
                    .path
                    .segments
                    .iter()
                    .map(|s| s.ident.to_string())
                    .collect::<Vec<_>>()
                    .join("::");
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
            Expr::const_(Name::from_string("Not"), vec![]),
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
            Ok(Expr::const_(Name::from_string(if value { "True" } else { "False" }), vec![]))
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
            let dom = atom_domain(ast, var_domains)?;
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
    let pre_ast: SynExpr = syn::parse_str(requires).map_err(|e| format!("requires parse: {e}"))?;
    let post_ast: SynExpr = syn::parse_str(ensures).map_err(|e| format!("ensures parse: {e}"))?;
    let mut vars = Vec::new();
    collect_vars(&pre_ast, &mut vars);
    collect_vars(&post_ast, &mut vars);
    let pre = elaborate_prop(&pre_ast, &vars, 0, dom)?;
    let post = elaborate_prop(&post_ast, &vars, 1, dom)?;
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
        // `/` and `%` are only ever built with a positive-literal divisor (the
        // elaborator gate), so `rhs == 0` here means a monitor was hand-built
        // outside the certified path — fail rather than panic.
        if matches!(op, ArithOp::Div | ArithOp::Rem) && rhs == 0 {
            return Err("monitor runtime: division or remainder by zero".into());
        }
        if self.is_signed() && matches!(op, ArithOp::Div | ArithOp::Rem) {
            return Err(format!(
                "monitor runtime: signed division/remainder is not implemented for `{}`",
                self.source_name()
            ));
        }
        match self.bits() {
            None => match op {
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
                let mask = bit_mask(bits);
                // Only `+`/`-`/`*` can overflow the width and need masking.
                // `/`/`%` and the bitwise ops of in-range operands are already
                // in range.
                match op {
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
        if !self.is_signed() {
            return Err(format!("`{}` is not a signed runtime carrier", self.source_name()));
        }
        let bits = self.bits().expect("signed carriers have a width");
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
        match expr {
            RuntimeMonitorExpr::Var(name) => {
                let actual = self
                    .domain(name)
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
                self.eval_term(lhs, values, domain)?,
                self.eval_term(rhs, values, domain)?,
                ArithOp::Add,
            ),
            RuntimeMonitorExpr::Sub(lhs, rhs) => domain.wrapping_bin(
                self.eval_term(lhs, values, domain)?,
                self.eval_term(rhs, values, domain)?,
                ArithOp::Sub,
            ),
            RuntimeMonitorExpr::Mul(lhs, rhs) => domain.wrapping_bin(
                self.eval_term(lhs, values, domain)?,
                self.eval_term(rhs, values, domain)?,
                ArithOp::Mul,
            ),
            RuntimeMonitorExpr::Div(lhs, rhs) => domain.wrapping_bin(
                self.eval_term(lhs, values, domain)?,
                self.eval_term(rhs, values, domain)?,
                ArithOp::Div,
            ),
            RuntimeMonitorExpr::Rem(lhs, rhs) => domain.wrapping_bin(
                self.eval_term(lhs, values, domain)?,
                self.eval_term(rhs, values, domain)?,
                ArithOp::Rem,
            ),
            RuntimeMonitorExpr::BitAnd(lhs, rhs) => domain.wrapping_bin(
                self.eval_term(lhs, values, domain)?,
                self.eval_term(rhs, values, domain)?,
                ArithOp::BitAnd,
            ),
            RuntimeMonitorExpr::BitOr(lhs, rhs) => domain.wrapping_bin(
                self.eval_term(lhs, values, domain)?,
                self.eval_term(rhs, values, domain)?,
                ArithOp::BitOr,
            ),
            RuntimeMonitorExpr::BitXor(lhs, rhs) => domain.wrapping_bin(
                self.eval_term(lhs, values, domain)?,
                self.eval_term(rhs, values, domain)?,
                ArithOp::BitXor,
            ),
            _ => Err("proposition used where a monitor term was required".into()),
        }
    }

    fn eval_prop(
        &self,
        expr: &RuntimeMonitorExpr,
        values: &std::collections::BTreeMap<&str, u128>,
    ) -> Result<bool, String> {
        let terms = |lhs: &RuntimeMonitorExpr, rhs: &RuntimeMonitorExpr| {
            let domain = self.term_domain(lhs, rhs)?;
            Ok::<_, String>((
                self.eval_term(lhs, values, domain)?,
                self.eval_term(rhs, values, domain)?,
            ))
        };
        match expr {
            RuntimeMonitorExpr::Eq(lhs, rhs) => {
                let (lhs, rhs) = terms(lhs, rhs)?;
                Ok(lhs == rhs)
            }
            RuntimeMonitorExpr::Le(lhs, rhs) => {
                let domain = self.term_domain(lhs, rhs)?;
                let (lhs, rhs) = terms(lhs, rhs)?;
                domain.compare(lhs, rhs, CompareOp::Le)
            }
            RuntimeMonitorExpr::Lt(lhs, rhs) => {
                let domain = self.term_domain(lhs, rhs)?;
                let (lhs, rhs) = terms(lhs, rhs)?;
                domain.compare(lhs, rhs, CompareOp::Lt)
            }
            RuntimeMonitorExpr::Ge(lhs, rhs) => {
                let domain = self.term_domain(lhs, rhs)?;
                let (lhs, rhs) = terms(lhs, rhs)?;
                domain.compare(lhs, rhs, CompareOp::Ge)
            }
            RuntimeMonitorExpr::Gt(lhs, rhs) => {
                let domain = self.term_domain(lhs, rhs)?;
                let (lhs, rhs) = terms(lhs, rhs)?;
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
        let evaluator = RuntimeMonitor {
            variables: self.variables.clone(),
            domains: self.domains.clone(),
            // `eval_term` does not inspect the outer proposition. Keeping the
            // exact term here avoids inventing a dummy comparison.
            expr: self.expr.clone(),
        };
        evaluator.eval_term(&self.expr, &values, self.domain)
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
                let bits = domain.bitvec_bits().expect("closed signed BitVec domain");
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
            Ok(Expr::bvar((vars.len() - 1 - pos) as u32 + offset))
        }
        RuntimeMonitorExpr::Zero => Ok(domain.zero()),
        RuntimeMonitorExpr::Lit(value) => match domain {
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
                |lhs, rhs| Expr::apps(Expr::const_(Name::from_string(op), vec![]), [lhs, rhs]);
            match domain {
                Domain::Nat => Ok(nat_bin(lhs, rhs)),
                Domain::Machine(width) => {
                    let carrier = width.carrier();
                    let lhs = Expr::app(
                        Expr::const_(Name::from_string(&format!("{carrier}.toNat")), vec![]),
                        lhs,
                    );
                    let rhs = Expr::app(
                        Expr::const_(Name::from_string(&format!("{carrier}.toNat")), vec![]),
                        rhs,
                    );
                    Ok(Expr::app(
                        Expr::const_(Name::from_string(&format!("{carrier}.ofNat")), vec![]),
                        nat_bin(lhs, rhs),
                    ))
                }
                Domain::U128 | Domain::USize(_) => {
                    let lhs = domain.bitvec_to_nat(lhs)?;
                    let rhs = domain.bitvec_to_nat(rhs)?;
                    domain.bitvec_of_nat(nat_bin(lhs, rhs))
                }
                Domain::Signed(_) | Domain::ISize(_) | Domain::Bool | Domain::OptionSigned(_) => {
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
                |lhs, rhs| Expr::apps(Expr::const_(Name::from_string(op), vec![]), [lhs, rhs]);
            match domain {
                Domain::Nat => Ok(nat_bin(lhs, rhs)),
                Domain::Machine(width) => {
                    let carrier = width.carrier();
                    let to_nat =
                        Expr::const_(Name::from_string(&format!("{carrier}.toNat")), vec![]);
                    let lhs = Expr::app(to_nat.clone(), lhs);
                    let rhs = Expr::app(to_nat, rhs);
                    Ok(Expr::app(
                        Expr::const_(Name::from_string(&format!("{carrier}.ofNat")), vec![]),
                        nat_bin(lhs, rhs),
                    ))
                }
                Domain::Signed(_) | Domain::U128 | Domain::USize(_) | Domain::ISize(_) => {
                    let lhs = domain.bitvec_to_nat(lhs)?;
                    let rhs = domain.bitvec_to_nat(rhs)?;
                    domain.bitvec_of_nat(nat_bin(lhs, rhs))
                }
                Domain::Bool => Err("bitwise operations are unsupported for bool".into()),
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
                _ => unreachable!(),
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
    Expr::app(Expr::const_(Name::from_string("Nat.succ"), vec![]), e)
}

/// `Eq.{1} Bool x <lit>` — the `x = true`/`x = false` proposition for a Bool
/// decision (`lit` = `Bool.true` / `Bool.false`).
fn bool_eq_expr(lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [Expr::const_(Name::from_string("Bool"), vec![]), lhs, rhs],
    )
}

fn bool_eq(x: Expr, lit: &str) -> Expr {
    bool_eq_expr(x, Expr::const_(Name::from_string(lit), vec![]))
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
    Expr::app(Expr::const_(Name::from_string("Not"), vec![]), p)
}

/// The `(small, large)` Nat operands of a comparison's `Nat.ble` at binder
/// `offset`: machine ints go through `<Carrier>.toNat` (the carrier's order IS
/// `toNat` order); `>=`/`>` swap the operands; the smaller side gets `succ` for
/// strict `<`/`>` (`Nat.lt a b ≡ Nat.le (succ a) b`). Shared by the positive
/// comparison monitor and the negation lane.
fn ble_operands(
    b: &syn::ExprBinary,
    vars: &[String],
    offset: u32,
    dom: &Domain,
) -> Result<(Expr, Expr), String> {
    // MONITOR LANE, SINGLE DOMAIN. `dom` is the atom's one domain (its caller
    // resolved it with `atom_domain` over the whole atom), so the per-variable
    // map is the uniform one — this reproduces the pre-increment typing of
    // every operand exactly.
    let var_domains = uniform_var_domains(vars, dom);
    let (swap, strict) = comparison_decision(&b.op)
        .ok_or_else(|| "monitor fragment: only <= < >= > are supported".to_string())?;
    let to_nat = |e: Expr| -> Expr {
        match dom {
            Domain::Nat => e,
            Domain::Machine(width) => Expr::app(
                Expr::const_(Name::from_string(&format!("{}.toNat", width.carrier())), vec![]),
                e,
            ),
            Domain::Signed(_) | Domain::U128 | Domain::USize(_) | Domain::ISize(_) => {
                dom.bitvec_order_key(e).expect("closed BitVec domain has an order key")
            }
            // `bool` ordering is rejected before a monitor is built; if reached,
            // the identity leaves a `Nat.ble` over a `Bool` that fails kernel
            // typecheck (a graceful error, never a panic). The Option carrier
            // is unordered for the same reason and takes the same identity.
            Domain::Bool | Domain::OptionSigned(_) => e,
        }
    };
    let l = to_nat(elab_term(&b.left, vars, offset, &var_domains, dom)?);
    let r = to_nat(elab_term(&b.right, vars, offset, &var_domains, dom)?);
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
    let (a0, b0) = ble_operands(b, vars, offset, dom)?;
    let ble = Expr::const_(Name::from_string("Nat.ble"), vec![]);
    let mon_body = Expr::app(Expr::app(ble, a0), b0);
    let (a1, b1) = ble_operands(b, vars, offset + 1, dom)?;
    // cond_true: `Nat.le_of_ble_eq_true a b h : Nat.le a b` (defeq to Nat.lt for
    // strict). cond_false: `Nat.not_le_of_ble_eq_false a b h : ¬(Nat.le a b)`.
    let sound = Expr::const_(Name::from_string("Nat.le_of_ble_eq_true"), vec![]);
    let compl = Expr::const_(Name::from_string("Nat.not_le_of_ble_eq_false"), vec![]);
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
        Domain::Nat => {
            let a0 = elab_term(&b.left, vars, offset, var_domains, dom)?;
            let b0 = elab_term(&b.right, vars, offset, var_domains, dom)?;
            let beq = Expr::const_(Name::from_string("Nat.beq"), vec![]);
            let mon_body = Expr::app(Expr::app(beq, a0), b0);
            let a1 = elab_term(&b.left, vars, offset + 1, var_domains, dom)?;
            let b1 = elab_term(&b.right, vars, offset + 1, var_domains, dom)?;
            let sound = Expr::const_(Name::from_string("Nat.eq_of_beq_eq_true"), vec![]);
            let compl = Expr::const_(Name::from_string("Nat.ne_of_beq_false"), vec![]);
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
            let dec_eq =
                Expr::const_(Name::from_string(&format!("{}.decEq", width.carrier())), vec![]);
            let decide = Expr::const_(Name::from_string("decide"), vec![]);
            let of_true = Expr::const_(Name::from_string("of_decide_eq_true"), vec![]);
            let of_false = Expr::const_(Name::from_string("of_decide_eq_false"), vec![]);
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
            let dec_eq = Expr::const_(Name::from_string("BitVec.decEq"), vec![]);
            let decide = Expr::const_(Name::from_string("decide"), vec![]);
            let of_true = Expr::const_(Name::from_string("of_decide_eq_true"), vec![]);
            let of_false = Expr::const_(Name::from_string("of_decide_eq_false"), vec![]);
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
    let dec_eq = Expr::const_(Name::from_string("Bool.decEq"), vec![]);
    let decide = Expr::const_(Name::from_string("decide"), vec![]);
    let of_true = Expr::const_(Name::from_string("of_decide_eq_true"), vec![]);
    let of_false = Expr::const_(Name::from_string("of_decide_eq_false"), vec![]);
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
            let not_c = Expr::const_(Name::from_string("Bool.not"), vec![]);
            let mon_body = Expr::app(not_c, mc0);
            // Trust: clean's prelude renamed these Bool negation bridges (FIDELITY /
            // KV-LIFT 2026-07-12) to avoid shadowing Lean 4's `Bool.not_eq_{true,false}`
            // (whose real statements are `Not (b = ·)` Prop-equalities, NOT these
            // `Bool.not b = · → b = ·` implications). Same statement, new names.
            let not_eq_true =
                Expr::const_(Name::from_string("Clean.Bool.eq_false_of_not_eq_true"), vec![]);
            let not_eq_false =
                Expr::const_(Name::from_string("Clean.Bool.eq_true_of_not_eq_false"), vec![]);
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
            let and_c = Expr::const_(Name::from_string("Bool.and"), vec![]);
            let mon_body = Expr::apps(and_c, [mon_p0, mon_q0]);
            // ── cond_true (offset+1): and_eq_true_left/right + And.intro ──
            let (mon_p1, ctp1, _cfp1) = build_mon_cond(&b.left, vars, offset + 1, var_domains)?;
            let (mon_q1, ctq1, _cfq1) = build_mon_cond(&b.right, vars, offset + 1, var_domains)?;
            let prop_p1 = elaborate_prop_multi(&b.left, vars, offset + 1, var_domains)?;
            let prop_q1 = elaborate_prop_multi(&b.right, vars, offset + 1, var_domains)?;
            let left_bridge = Expr::const_(Name::from_string("Bool.and_eq_true_left"), vec![]);
            let right_bridge = Expr::const_(Name::from_string("Bool.and_eq_true_right"), vec![]);
            let hp = Expr::apps(left_bridge, [mon_p1.clone(), mon_q1.clone(), Expr::bvar(0)]);
            let hq = Expr::apps(right_bridge, [mon_p1.clone(), mon_q1.clone(), Expr::bvar(0)]);
            let and_intro = Expr::const_(Name::from_string("And.intro"), vec![]);
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
            let not_and_left = Expr::const_(Name::from_string("not_and_of_not_left"), vec![]);
            let not_and_right = Expr::const_(Name::from_string("not_and_of_not_right"), vec![]);
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
            let and_false_elim = Expr::const_(Name::from_string("Bool.and_eq_false_elim"), vec![]);
            let cf_body =
                Expr::apps(and_false_elim, [mon_p1, mon_q1, neg_and1, Expr::bvar(0), fa, fb]);
            let cond_false =
                Expr::lam(BinderInfo::Default, bool_eq_false(mon_body.clone()), cf_body);
            Ok((mon_body, cond_true, cond_false))
        }
        SynExpr::Binary(b) if matches!(b.op, BinOp::Or(_)) => {
            let (mon_p0, _, _) = build_mon_cond(&b.left, vars, offset, var_domains)?;
            let (mon_q0, _, _) = build_mon_cond(&b.right, vars, offset, var_domains)?;
            let or_c = Expr::const_(Name::from_string("Bool.or"), vec![]);
            let mon_body = Expr::apps(or_c, [mon_p0, mon_q0]);
            let prop_p1 = elaborate_prop_multi(&b.left, vars, offset + 1, var_domains)?;
            let prop_q1 = elaborate_prop_multi(&b.right, vars, offset + 1, var_domains)?;
            // ── cond_true (offset+1 args, offset+2 case fns): or_eq_true_elim ──
            let (mon_p1, _ctp1, _cfp1) = build_mon_cond(&b.left, vars, offset + 1, var_domains)?;
            let (mon_q1, _ctq1, _cfq1) = build_mon_cond(&b.right, vars, offset + 1, var_domains)?;
            let result_ty = connective("Or", prop_p1.clone(), prop_q1.clone());
            let (_, ctp2, _) = build_mon_cond(&b.left, vars, offset + 2, var_domains)?;
            let (_, ctq2, _) = build_mon_cond(&b.right, vars, offset + 2, var_domains)?;
            let prop_p2 = elaborate_prop_multi(&b.left, vars, offset + 2, var_domains)?;
            let prop_q2 = elaborate_prop_multi(&b.right, vars, offset + 2, var_domains)?;
            let or_inl = Expr::const_(Name::from_string("Or.inl"), vec![]);
            let or_inr = Expr::const_(Name::from_string("Or.inr"), vec![]);
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
            let or_true_elim = Expr::const_(Name::from_string("Bool.or_eq_true_elim"), vec![]);
            let ct_body = Expr::apps(
                or_true_elim,
                [mon_p1.clone(), mon_q1.clone(), result_ty, Expr::bvar(0), fa, fb],
            );
            let cond_true = Expr::lam(BinderInfo::Default, bool_eq_true(mon_body.clone()), ct_body);
            // ── cond_false (offset+1): or_eq_false_elim → both false → ¬(P∨Q) ──
            // The continuation `k` opens TWO binders (hp, hq), so the conjuncts are
            // at offset+3: `hp` is bvar 1, `hq` is bvar 0.
            let mon_q2 = build_mon_cond(&b.right, vars, offset + 2, var_domains)?.0;
            let (_, _, cfp3) = build_mon_cond(&b.left, vars, offset + 3, var_domains)?;
            let (_, _, cfq3) = build_mon_cond(&b.right, vars, offset + 3, var_domains)?;
            let prop_p3 = elaborate_prop_multi(&b.left, vars, offset + 3, var_domains)?;
            let prop_q3 = elaborate_prop_multi(&b.right, vars, offset + 3, var_domains)?;
            let neg_or1 = not_prop(connective("Or", prop_p1, prop_q1));
            let not_or = Expr::const_(Name::from_string("not_or_intro"), vec![]);
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
            let or_false_elim = Expr::const_(Name::from_string("Bool.or_eq_false_elim"), vec![]);
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
        SynExpr::Path(_) if atom_domain(ast, var_domains)?.is_bool() => {
            let dom = atom_domain(ast, var_domains)?;
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
        let mon2 = build_mon_cond(ast, vars, 2, var_domains)?.0;
        let motive = Expr::lam(
            BinderInfo::Default,
            Expr::const_(Name::from_string("Bool"), vec![]),
            Expr::pi(
                BinderInfo::Default,
                bool_eq_expr(mon2, Expr::bvar(0)),
                bool_eq_true(Expr::bvar(1)),
            ),
        );

        let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
        let bfalse = Expr::const_(Name::from_string("Bool.false"), vec![]);
        let btrue = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]);
        let refl_true = Expr::apps(eq_refl.clone(), [bool_ty.clone(), btrue.clone()]);

        // false branch: λ he : mon=false, False.elim (false=true)
        //   ((cond_false he) hp)
        let false_branch = {
            let (_, _, cond_false2) = build_mon_cond(ast, vars, 2, var_domains)?;
            let contradiction = Expr::app(Expr::app(cond_false2, Expr::bvar(0)), Expr::bvar(1));
            let false_elim = Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]);
            let false_eq_true = bool_eq_true(bfalse.clone());
            Expr::lam(
                BinderInfo::Default,
                bool_eq(mon1.clone(), "Bool.false"),
                Expr::apps(false_elim, [false_eq_true, contradiction]),
            )
        };
        // true branch: λ _ : mon=true, rfl.
        let true_branch = Expr::lam(BinderInfo::Default, bool_eq_true(mon1.clone()), refl_true);
        let cases_on = Expr::const_(Name::from_string("Bool.casesOn"), vec![Level::zero()]);
        let cases = Expr::apps(cases_on, [motive, mon1.clone(), false_branch, true_branch]);
        let refl_mon = Expr::apps(eq_refl, [bool_ty, mon1]);
        Expr::lam(BinderInfo::Default, prop.clone(), Expr::app(cases, refl_mon))
    };

    let iff_goal =
        Expr::apps(Expr::const_(Name::from_string("Iff"), vec![]), [eq_true.clone(), prop.clone()]);
    let iff_proof = Expr::apps(
        Expr::const_(Name::from_string("Iff.intro"), vec![]),
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
        Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]),
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
    /// `Bool`.
    Bool,
    /// `UInt8` / `UInt16` / `UInt32` / `UInt64` — the wrapping unsigned carriers.
    UInt(MachineUIntWidth),
    /// `BitVec N`.
    BitVec(u32),
    /// `Option <inner>`.
    Option(Box<Carrier>),
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
            Carrier::Nat => Some(Domain::Nat),
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
            Carrier::Nat => "Nat".to_string(),
            Carrier::Bool => "Bool".to_string(),
            Carrier::UInt(width) => width.carrier().to_string(),
            Carrier::BitVec(bits) => format!("BitVec {bits}"),
            Carrier::Option(inner) => format!("Option ({})", inner.clean_name()),
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
    let inst_c = |s: &str| Expr::const_(Name::from_string(s), vec![]);
    Ok(match d {
        Domain::Machine(w) => {
            let carrier = w.carrier();
            match cmp {
                SelectCmp::Lt => (
                    Expr::apps(
                        Expr::const_(Name::from_string("LT.lt"), vec![zero.clone()]),
                        [ty.clone(), inst_c(&format!("instLT{carrier}")), l.clone(), r.clone()],
                    ),
                    Expr::apps(inst_c(&format!("instDecidable{carrier}Lt")), [l, r]),
                ),
                SelectCmp::Le => (
                    Expr::apps(
                        Expr::const_(Name::from_string("LE.le"), vec![zero.clone()]),
                        [ty.clone(), inst_c(&format!("instLE{carrier}")), l.clone(), r.clone()],
                    ),
                    Expr::apps(inst_c(&format!("instDecidable{carrier}Le")), [l, r]),
                ),
                SelectCmp::Eq => (
                    Expr::apps(
                        Expr::const_(Name::from_string("Eq"), vec![one.clone()]),
                        [ty.clone(), l.clone(), r.clone()],
                    ),
                    Expr::apps(inst_c(&format!("instDecidableEq{carrier}")), [l, r]),
                ),
            }
        }
        Domain::Signed(_) => {
            let key = |e: Expr| d.bitvec_order_key(e).expect("closed signed BitVec domain");
            match cmp {
                SelectCmp::Lt => {
                    let (kl, kr) = (key(l), key(r));
                    (
                        nat_pred("Nat.lt", kl.clone(), kr.clone()),
                        Expr::apps(inst_c("Nat.decLt"), [kl, kr]),
                    )
                }
                SelectCmp::Le => {
                    let (kl, kr) = (key(l), key(r));
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
                            Expr::const_(Name::from_string("Eq"), vec![one.clone()]),
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
            if admission.param_names.as_ref().is_some_and(|minted| *minted != param_names) {
                let minted = admission.param_names.as_ref().expect("checked just above");
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
    let admission = ambient_admission(&callee_path(c))?;
    admission.carriers.filter(|carriers| carriers.params.len() == admission.arity)
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
        SynExpr::Binary(b) => {
            collect_ambient_vars(&b.left, out);
            collect_ambient_vars(&b.right, out);
        }
        SynExpr::Unary(u) => collect_ambient_vars(&u.expr, out),
        // THE ONE DIFFERENCE from `collect_vars`: a call whose callee declares
        // its own parameter carriers contributes NO ambient operands.
        SynExpr::Call(c) => {
            if typed_callee_carriers(c).is_none() {
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
        leaf => {
            let mut names = Vec::new();
            collect_vars(leaf, &mut names);
            for v in names {
                if !out.contains(&v) {
                    out.push(v);
                }
            }
        }
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
            // admissions, the same precedence as everywhere on this path.
            if let Some(admission) = ambient_admission(v) {
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
/// This runs only on the two paths that did not exist before increment 8 (a
/// variable-free atom and a recovered mixed-domain atom), so it can refuse
/// nothing that used to be accepted; on those paths it turns what would have
/// been a downstream ill-typed goal into a named refusal at the clause.
fn check_ambient_call_result_carriers(atom: &SynExpr, dom: &Domain) -> Result<(), String> {
    let mut calls = Vec::new();
    collect_ambient_calls(atom, &mut calls);
    for c in &calls {
        let Some(carriers) = typed_callee_carriers(c) else { continue };
        if carriers.ret != dom.carrier() {
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
    }
    Ok(())
}

/// The CALL expressions in an atom's ambient positions — the same walk as
/// [`collect_ambient_vars`], so a call nested inside a typed call's argument
/// list is skipped for the same reason its variables are: it is typed by that
/// callee's declaration, not by the enclosing comparison.
fn collect_ambient_calls<'a>(e: &'a SynExpr, out: &mut Vec<&'a syn::ExprCall>) {
    match e {
        SynExpr::Paren(p) => collect_ambient_calls(&p.expr, out),
        SynExpr::Binary(b) => {
            collect_ambient_calls(&b.left, out);
            collect_ambient_calls(&b.right, out);
        }
        SynExpr::Unary(u) => collect_ambient_calls(&u.expr, out),
        SynExpr::Call(c) => {
            out.push(c);
            if typed_callee_carriers(c).is_none() {
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

/// The callee path of a call expression, exactly as the facet/admission table
/// keys it (`min` or `cmp::min`). A non-path callee has no item identity and is
/// reported as `<expression>`, which never matches an admission key — so it
/// stays fail-closed.
fn callee_path(c: &syn::ExprCall) -> String {
    match &*c.func {
        SynExpr::Path(p) => {
            p.path.segments.iter().map(|s| s.ident.to_string()).collect::<Vec<_>>().join("::")
        }
        _ => "<expression>".to_string(),
    }
}

/// The E6 return domain of a CALL whose callee is in the ambient admission
/// table, or `None` for an unadmitted callee / an admission that does not
/// record one (see [`Admission::ret_domain`]).
fn call_ret_domain(c: &syn::ExprCall) -> Option<Domain> {
    ambient_admission(&callee_path(c)).and_then(|a| a.return_domain().cloned())
}

/// The `Option<iN>` payload width of a CALL whose callee is admitted with an
/// [`Domain::OptionSigned`] return domain, else `None`.
fn call_option_ret_width(e: &SynExpr) -> Option<MachineSIntWidth> {
    let SynExpr::Call(c) = e else { return None };
    match call_ret_domain(c) {
        Some(Domain::OptionSigned(width)) => Some(width),
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
        SynExpr::Call(c) => callee_path(c) == "Some",
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
    let bool_op = |name: &str, args: Vec<Expr>| {
        Expr::apps(Expr::const_(Name::from_string(name), vec![]), args)
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
        // Concrete values as RAW Nat literals — the kernel's own canonical
        // BitVec value form (see the BitVec native reducers: `BitVec.ofNat`
        // COLLAPSES to the raw literal, and `BitVec.toNat`/comparisons fire on
        // it, whereas a projection on the wrapped `ofNat` spelling parks).
        // The first row pins that the two spellings coincide definitionally,
        // so every later row is also evidence about the `ofNat` form.
        let p = |v: u64| kernel_nat_lit(u128::from(v));
        // Negative value -v as its two's-complement 64-bit pattern.
        let m = |v: u64| kernel_nat_lit(0u128.wrapping_sub(u128::from(v)) & bit_mask(64));
        assert!(
            tc.is_def_eq(&i.numeral(3).unwrap(), &p(3)),
            "BitVec.ofNat 64 3 is definitionally the raw literal 3"
        );
        assert!(
            tc.is_def_eq(&i.negative_numeral(1).unwrap(), &m(1)),
            "the negative_numeral embedding is definitionally its bit pattern"
        );
        let app2 = |f: &str, a: Expr, b: Expr| {
            Expr::apps(Expr::const_(Name::from_string(f), vec![]), [a, b])
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
        let min64 = kernel_nat_lit(1u128 << 63);
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
            Expr::apps(Expr::const_(Name::from_string(f), vec![]), [a, b])
        };
        // u64 rows: UInt64 values are the carrier's own numerals.
        let un = |v: u64| u.numeral(u128::from(v)).unwrap();
        assert!(tc.is_def_eq(&app2("ule_def", un(3), un(5)), &btrue), "u64: 3 <= 5");
        assert!(tc.is_def_eq(&app2("ule_def", un(5), un(3)), &bfalse), "u64: !(5 <= 3)");
        // i64 rows: raw Nat literals are the kernel-canonical BitVec form
        // (see the signed select test above for why).
        let p = |v: u64| kernel_nat_lit(u128::from(v));
        let m = |v: u64| kernel_nat_lit(0u128.wrapping_sub(u128::from(v)) & bit_mask(64));
        assert!(tc.is_def_eq(&app2("sle_def", p(3), p(5)), &btrue), "i64: 3 <= 5");
        assert!(tc.is_def_eq(&app2("sle_def", p(5), p(3)), &bfalse), "i64: !(5 <= 3)");
        // MIXED-SIGN rows.
        assert!(tc.is_def_eq(&app2("sle_def", m(1), p(1)), &btrue), "i64: -1 <= 1");
        assert!(tc.is_def_eq(&app2("sle_def", p(1), m(1)), &bfalse), "i64: !(1 <= -1)");
        let min64 = kernel_nat_lit(1u128 << 63);
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
            Expr::apps(Expr::const_(Name::from_string(f), vec![]), [a, b])
        };
        // Concrete values as RAW Nat literals — the kernel's canonical BitVec
        // value form, the same convention the i64 rows above use.
        let v = |x: i128| kernel_nat_lit(x as u128);
        assert!(
            tc.is_def_eq(&d.numeral(3).unwrap(), &v(3)),
            "BitVec.ofNat 128 3 is definitionally the raw literal 3"
        );
        assert!(tc.is_def_eq(&app2("wle_def", v(3), v(5)), &btrue), "i128: 3 <= 5");
        assert!(tc.is_def_eq(&app2("wle_def", v(5), v(3)), &bfalse), "i128: !(5 <= 3)");
        assert!(tc.is_def_eq(&app2("wmin_def", v(3), v(5)), &v(3)), "i128: min2(3, 5) = 3");

        // MULTI-LIMB NUMERAL COLLAPSE, now positive evidence. The kernel's
        // `BitVec.ofNat` reducer reads its value at arbitrary magnitude
        // (`0 ≤ N < 2^128`, bare literal or OfNat-wrapped) and emits a
        // multi-limb payload, so `BitVec.ofNat 128 pattern ≡ pattern` holds for
        // every i128 bit pattern — including the multi-limb negative ones.
        // These rows pin the collapse at the three boundary patterns:
        // i64::MIN's 128-bit pattern (2^128 − 2^63), i64::MAX, and i128::MIN.
        assert!(
            tc.is_def_eq(&d.negative_numeral(1u128 << 63).unwrap(), &v(i128::from(i64::MIN))),
            "BitVec.ofNat 128 (2^128 − 2^63) collapses to the raw multi-limb pattern"
        );
        assert!(
            tc.is_def_eq(&d.numeral(i64::MAX as u128).unwrap(), &v(i128::from(i64::MAX))),
            "BitVec.ofNat 128 i64::MAX collapses to the raw literal"
        );
        assert!(
            tc.is_def_eq(&d.negative_numeral(1u128 << 127).unwrap(), &v(i128::MIN)),
            "BitVec.ofNat 128 (2^127) — i128::MIN's pattern — collapses multi-limb"
        );

        // `BitVec.toNat` NOW REDUCES at every magnitude (the former limit was
        // pinned here and fired when the reducer grew multi-limb support plus
        // the structural `ofNat` peel — this block is the same-commit answer
        // its message demanded). First the identity itself, at the pattern
        // that used to park:
        assert!(
            tc.is_def_eq(&d.bitvec_to_nat(v(-1)).unwrap(), &v(-1)),
            "BitVec.toNat of a multi-limb payload is the payload"
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
