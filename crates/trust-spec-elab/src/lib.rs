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
                if !out.contains(&s) {
                    out.push(s);
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
fn elab_term(e: &SynExpr, vars: &[String], offset: u32, dom: &Domain) -> Result<Expr, String> {
    match e {
        SynExpr::Paren(p) => elab_term(&p.expr, vars, offset, dom),
        SynExpr::Path(p) => {
            let id = p
                .path
                .get_ident()
                .ok_or_else(|| "only bare identifiers are supported".to_string())?
                .to_string();
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
            let value = elab_term(&u.expr, vars, offset, dom)?;
            dom.arithmetic("sub", dom.zero(), value)
        }
        SynExpr::Binary(b) => {
            // `bool` has no arithmetic — `+ - * / %` over a boolean binding
            // fail closed (only `==`/`!=`, the connectives, and a bare bool are
            // supported for `bool`).
            if matches!(dom, Domain::Bool) {
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
                let dividend = elab_term(&b.left, vars, offset, dom)?;
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
                let finite_bits = match dom {
                    Domain::Machine(w) => Some(w.bits()),
                    _ => dom.bitvec_bits(),
                };
                if let Some(bits) = finite_bits {
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
                let l = elab_term(&b.left, vars, offset, dom)?;
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
                let l = elab_term(&b.left, vars, offset, dom)?;
                let r = elab_term(&b.right, vars, offset, dom)?;
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
            let l = elab_term(&b.left, vars, offset, dom)?;
            let r = elab_term(&b.right, vars, offset, dom)?;
            dom.arithmetic(op, l, r)
        }
        // E6 (design §3.1/§1.2-1): a program-fn call is a definitional use —
        // admissible only with a certified Pure ∧ Total ∧ Deterministic ∧
        // NoPanic facet AND a kernel constant minted by the import step; a
        // non-admitted call fails closed with the E6 diagnostic below.
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
            // E6 brick 4: an ADMITTED call elaborates to its kernel constant
            // applied to the elaborated arguments. The constant carries a
            // kernel-rechecked defining equation (minted by the import step);
            // the ambient admission table gates on certified facets + a minted
            // constant, so this fires only for genuinely admitted functions.
            if let Some(admission) = ambient_admission(&callee) {
                if admission.arity != c.args.len() {
                    return Err(format!(
                        "admitted `{callee}` has arity {} but is applied to {} argument(s)",
                        admission.arity,
                        c.args.len()
                    ));
                }
                let mut applied = Expr::const_(Name::from_string(&admission.kernel_const), vec![]);
                for arg in &c.args {
                    applied = Expr::app(applied, elab_term(arg, vars, offset, dom)?);
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
        // A bare identifier is a proposition only in a `bool` clause, where
        // `flag` is read as `flag = true`.
        SynExpr::Path(_) if matches!(dom, Domain::Bool) => {
            let v = elab_term(ast, vars, offset, dom)?;
            Ok(dom.eq(v, dom.bool_lit(true)?))
        }
        // A boolean literal is the trivial proposition `True`/`False`.
        SynExpr::Lit(l) if matches!(&l.lit, Lit::Bool(_)) => {
            let value = matches!(&l.lit, Lit::Bool(b) if b.value);
            Ok(Expr::const_(Name::from_string(if value { "True" } else { "False" }), vec![]))
        }
        // Comparison predicate `a <cmp> b`: operands are *terms*.
        SynExpr::Binary(b) => {
            // `bool` is unordered — only `==`/`!=` decide it.
            if matches!(dom, Domain::Bool)
                && matches!(b.op, BinOp::Le(_) | BinOp::Lt(_) | BinOp::Ge(_) | BinOp::Gt(_))
            {
                return Err("`bool` values are not ordered (use `==` or `!=`)".into());
            }
            let l = elab_term(&b.left, vars, offset, dom)?;
            let r = elab_term(&b.right, vars, offset, dom)?;
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
        // admission authority. Admission fires only for calls in TERM position
        // (`elab_term`'s call arm applies the minted kernel constant); a call
        // in PROPOSITION position is outside the admitted fragment, so this
        // arm always fails CLOSED with the diagnostic below.
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
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Admission {
    /// The Clean kernel constant name the function was admitted as.
    pub kernel_const: String,
    /// The function's arity (number of value parameters) — the elaborator
    /// applies the constant to exactly this many arguments.
    pub arity: usize,
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
    pub fn admitted(&self, callee_path: &str) -> Option<&Admission> {
        let certified = self.map.get(callee_path).is_some_and(FnFacets::admissible);
        if certified { self.admissions.get(callee_path) } else { None }
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
    Ok(Admission { kernel_const: kernel_const.to_string(), arity: 0 })
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
    Ok(Admission { kernel_const: kernel_const.to_string(), arity: n })
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
    let term = elab_term(&syn, &names, 0, domain)?;
    let var_domains: std::collections::BTreeMap<String, Domain> =
        names.iter().map(|n| (n.clone(), domain.clone())).collect();
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
    Ok(Admission { kernel_const: kernel_const.to_string(), arity: n })
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
/// eliminator (`Bool.rec motive false_case true_case scrutinee`). Single machine
/// domain; `add_decl` FULL-KERNEL-CHECKS the result and a wrong construction is
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
    let zero = Level::zero();
    let one = Level::succ(Level::zero());
    let (l, r) = (bvar(cmp_left), bvar(cmp_right)); // carrier level — NOT .toNat
    let inst_c = |s: &str| Expr::const_(Name::from_string(s), vec![]);
    let (prop, inst) = match cmp {
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
    };
    // ARGUMENT ORDER: `ite α c h t e` takes THEN fourth and ELSE fifth, the
    // opposite of `Bool.rec`, which took ELSE first. Reversing these silently
    // mints `max` where the program wrote `min`, and the E9 goal still closes
    // whenever the island happens to be reversed the same way — so a positive
    // fixture alone does NOT catch it. The paired NEG probe is the net.
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
    .map_err(|e| format!("kernel rejected the select defining equation: {e:?}"))?;
    Ok(Admission { kernel_const: kernel_const.to_string(), arity: n })
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
}

/// RAII guard that installs an ambient [`FacetTable`] for admission-aware
/// elaboration and RESTORES the previous value on drop — so a nested
/// elaboration cannot leak its table to an outer one, and a panic mid-
/// elaboration cannot leave a stale table behind.
struct AdmissionScope {
    previous: Option<FacetTable>,
}

impl AdmissionScope {
    fn enter(facets: FacetTable) -> Self {
        let previous = ADMISSION_FACETS.with(|slot| slot.replace(Some(facets)));
        AdmissionScope { previous }
    }
}

impl Drop for AdmissionScope {
    fn drop(&mut self) {
        ADMISSION_FACETS.with(|slot| *slot.borrow_mut() = self.previous.take());
    }
}

/// Consult the ambient admission table for `callee`'s minted kernel constant.
fn ambient_admission(callee: &str) -> Option<Admission> {
    ADMISSION_FACETS
        .with(|slot| slot.borrow().as_ref().and_then(|table| table.admitted(callee).cloned()))
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
    // E3: a quantified clause is not syn-parseable as a whole, so the facet
    // diagnostic walk runs over the pre-parsed leaves instead; the admission
    // scope then covers the same quantified elaboration path.
    if clause_uses_quantifier_fragment(spec) {
        let clause = parse_qclause(spec, true)?;
        if let Some(err) = qclause_first_call_facet_error(&clause, facets) {
            return Err(err);
        }
        let _scope = AdmissionScope::enter(facets.clone());
        return elaborate_goal_typed(spec, var_types);
    }
    let ast: SynExpr = syn::parse_str(spec).map_err(|e| format!("parse error: {e}"))?;
    if let Some(err) = first_call_facet_error(&ast, facets) {
        return Err(err);
    }
    let _scope = AdmissionScope::enter(facets.clone());
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
    // A clause that never mentions `result` is a ∀-params statement independent
    // of the function's return value — its proof covers the postcondition for
    // ANY body, so the SELF-admission gate is required only when `result` must
    // be substituted with the defining equation. (Calls inside the clause are
    // still individually gated on THEIR admissions by the elaborator.)
    if !mentions_result(&ast) {
        let used = discharge_used_bindings(clause, param_types);
        return elaborate_goal_typed_with_facets(clause, &used, facets);
    }
    if facets.admitted(self_fn_name).is_none() {
        // `result` has no kernel denotation unless the function is E6-admitted;
        // fail closed (design note §3 restriction), same as any un-admitted call.
        return Err(format!(
            "ensures discharge requires the specified function `{self_fn_name}` to be \
             E6-admitted (its defining equation kernel-imported); it is not"
        ));
    }
    // Build the substitute `self_fn(p0, p1, …)` once, then splice it in for every
    // `result`. Parsing a synthesized call string reuses syn's own node shapes.
    let call_src = format!("{self_fn_name}({})", param_names.join(", "));
    let self_call: SynExpr = syn::parse_str(&call_src)
        .map_err(|e| format!("internal: could not build self-call `{call_src}`: {e}"))?;
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
        _ => false,
    }
}

/// Structurally replace every bare `result` identifier in a clause AST with
/// `replacement` (the `self_fn(params…)` call). Only the clause-expression node
/// shapes the elaborator supports are traversed; anything else is returned
/// unchanged (it will fail closed in the elaborator, not here). NOTE: a `result`
/// appearing as a call's CALLEE is not a clause variable and is left alone —
/// consistent with `collect_vars`, which never treats a callee path as a variable.
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
/// type (`x == flag` mixing `u64` and `bool` fails closed). A variable-free
/// atom (`2 < 3`) defaults to `Nat`; a literal adopts the atom's domain.
fn atom_domain(atom: &SynExpr, var_domains: &BTreeMap<String, Domain>) -> Result<Domain, String> {
    let mut vs = Vec::new();
    collect_vars(atom, &mut vs);
    let mut dom: Option<Domain> = None;
    for v in &vs {
        let d = var_domains.get(v).ok_or_else(|| format!("unbound variable `{v}`"))?;
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
    Ok(dom.unwrap_or(Domain::Nat))
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
        // A bare identifier is a proposition only for a `bool` binding.
        SynExpr::Path(_) => {
            let dom = atom_domain(ast, var_domains)?;
            if !matches!(dom, Domain::Bool) {
                return Err("a bare identifier is a proposition only for a `bool` binding".into());
            }
            let v = elab_term(ast, vars, offset, &dom)?;
            Ok(dom.eq(v, dom.bool_lit(true)?))
        }
        SynExpr::Binary(b) => {
            let dom = atom_domain(ast, var_domains)?;
            if matches!(dom, Domain::Bool)
                && matches!(b.op, BinOp::Le(_) | BinOp::Lt(_) | BinOp::Ge(_) | BinOp::Gt(_))
            {
                return Err("`bool` values are not ordered (use `==` or `!=`)".into());
            }
            let l = elab_term(&b.left, vars, offset, &dom)?;
            let r = elab_term(&b.right, vars, offset, &dom)?;
            Ok(match b.op {
                BinOp::Eq(_) => dom.eq(l, r),
                BinOp::Le(_) => dom.cmp("le", l, r),
                BinOp::Lt(_) => dom.cmp("lt", l, r),
                BinOp::Ge(_) => dom.cmp("le", r, l),
                BinOp::Gt(_) => dom.cmp("lt", r, l),
                _ => return Err("comparison op must be one of == != <= < >= >".into()),
            })
        }
        // Program-function / method calls fail closed (E6) — the diagnostic is
        // domain-independent, so reuse the single-domain arm.
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
                if matches!(domain, Domain::Bool) {
                    return Err("monitor runtime: an integer literal is not a `bool`".into());
                }
                let _ = domain.numeral(n)?;
                if n == 0 { Ok(RuntimeMonitorExpr::Zero) } else { Ok(RuntimeMonitorExpr::Lit(n)) }
            }
            Lit::Bool(b) if matches!(domain, Domain::Bool) => {
                Ok(RuntimeMonitorExpr::Lit(u128::from(b.value)))
            }
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
            if matches!(domain, Domain::Bool) {
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
                Domain::Signed(_) | Domain::ISize(_) | Domain::Bool => {
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
            if !matches!(var_domains.get(&id), Some(Domain::Bool)) {
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
            if matches!(domain, Domain::Bool)
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
            // typecheck (a graceful error, never a panic).
            Domain::Bool => e,
        }
    };
    let l = to_nat(elab_term(&b.left, vars, offset, dom)?);
    let r = to_nat(elab_term(&b.right, vars, offset, dom)?);
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
    match dom {
        Domain::Nat => {
            let a0 = elab_term(&b.left, vars, offset, dom)?;
            let b0 = elab_term(&b.right, vars, offset, dom)?;
            let beq = Expr::const_(Name::from_string("Nat.beq"), vec![]);
            let mon_body = Expr::app(Expr::app(beq, a0), b0);
            let a1 = elab_term(&b.left, vars, offset + 1, dom)?;
            let b1 = elab_term(&b.right, vars, offset + 1, dom)?;
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
            let a0 = elab_term(&b.left, vars, offset, dom)?;
            let b0 = elab_term(&b.right, vars, offset, dom)?;
            let eq_prop0 = dom.eq(a0.clone(), b0.clone());
            let inst0 = Expr::apps(dec_eq.clone(), [a0, b0]);
            let mon_body = Expr::apps(decide, [eq_prop0, inst0]);
            // certificates cite of_decide_* at the same `Eq`/instance, offset+1.
            let a1 = elab_term(&b.left, vars, offset + 1, dom)?;
            let b1 = elab_term(&b.right, vars, offset + 1, dom)?;
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
            let a0 = elab_term(&b.left, vars, offset, dom)?;
            let b0 = elab_term(&b.right, vars, offset, dom)?;
            let eq_prop0 = dom.eq(a0.clone(), b0.clone());
            let inst0 = Expr::apps(dec_eq.clone(), [width.clone(), a0, b0]);
            let mon_body = Expr::apps(decide, [eq_prop0, inst0]);
            let a1 = elab_term(&b.left, vars, offset + 1, dom)?;
            let b1 = elab_term(&b.right, vars, offset + 1, dom)?;
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
            let a0 = elab_term(&b.left, vars, offset, dom)?;
            let b0 = elab_term(&b.right, vars, offset, dom)?;
            let a1 = elab_term(&b.left, vars, offset + 1, dom)?;
            let b1 = elab_term(&b.right, vars, offset + 1, dom)?;
            Ok(bool_eq_mon_cond(a0, b0, a1, b1, dom))
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
        // Equality / comparison / bare-bool ATOMS take the single domain shared
        // by their variables (`atom_domain`); the connective arms above stay
        // domain-agnostic.
        SynExpr::Binary(b) if matches!(b.op, BinOp::Eq(_)) => {
            equality_mon_cond(b, vars, offset, &atom_domain(ast, var_domains)?)
        }
        // A bare boolean `flag` decides as `flag == true` — the same certified
        // equality monitor with `Bool.true` as the right operand.
        SynExpr::Path(_) if matches!(atom_domain(ast, var_domains)?, Domain::Bool) => {
            let dom = atom_domain(ast, var_domains)?;
            let a0 = elab_term(ast, vars, offset, &dom)?;
            let a1 = elab_term(ast, vars, offset + 1, &dom)?;
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
    if matches!(domain, Domain::Bool) {
        return Err("a scalar measure cannot use the `bool` carrier".into());
    }
    let source_body = elab_term(ast, vars, 0, domain)?;
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
        table.admit("crate::f", Admission { kernel_const: "f_def".into(), arity: 1 });
        table.admit("crate::g", Admission { kernel_const: "g_def".into(), arity: 1 });
        assert_eq!(
            table.admitted("crate::f"),
            Some(&Admission { kernel_const: "f_def".into(), arity: 1 })
        );
        assert_eq!(
            table.admitted("crate::g"),
            None,
            "a non-admissible facet record cannot be admitted"
        );
    }

    #[test]
    fn admit_constant_function_mints_a_kernel_checked_admission() {
        // `fn answer() -> u64 { 42 }`: the minimal E6 kernel-import. The kernel
        // must accept the defining equation and then KNOW the constant.
        let mut env = Environment::with_prelude();
        let adm = admit_constant_function(&mut env, "answer_def", 42, MachineUIntWidth::U64)
            .expect("a constant u64 function must admit");
        assert_eq!(adm, Admission { kernel_const: "answer_def".to_string(), arity: 0 });

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
    fn admit_expr_function_mints_a_semantically_correct_arithmetic_admission() {
        let mut env = Environment::with_prelude();
        let u = Domain::Machine(MachineUIntWidth::U64);
        // fn winc(x: u64) -> u64 { x.wrapping_add(1) }  (machine `+` is wrapping)
        let adm = admit_expr_function(&mut env, "winc_def", "x + 1", &["x"], &u)
            .expect("wrapping-add function must admit");
        assert_eq!(adm, Admission { kernel_const: "winc_def".to_string(), arity: 1 });

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
        assert_eq!(adm, Admission { kernel_const: "fst_def".to_string(), arity: 2 });

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
        facets.admit("f", Admission { kernel_const: "f_def".to_string(), arity: 1 });

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

        let adm = || Admission { kernel_const: "min2".into(), arity: 2 };

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
        t.admit("min2", Admission { kernel_const: "min2".into(), arity: 2 });

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

#[cfg(test)]
mod quantifier_tests {
    use clean_kernel::{Environment, ExprKind, TypeChecker};

    use super::*;

    /// `Prop` — the sort a well-formed clause goal must inhabit.
    fn prop() -> Expr {
        Expr::sort(Level::zero())
    }

    /// `<op-const> a b` over a domain, mirroring `elab_term`'s binary encoding.
    fn dom_bin(dom: &Domain, which: &str, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(Expr::const_(Name::from_string(&dom.op(which)), vec![]), a), b)
    }

    #[test]
    fn forall_goal_elaborates_and_typechecks_as_prop() {
        let env = Environment::with_prelude();
        let tc = TypeChecker::new(&env);
        let goal = elaborate_goal_typed("forall i: u64, i + 0 == i", &[])
            .expect("a closed forall clause must elaborate");
        let ty = tc.infer_type(&goal).expect("forall goal must be well-typed in the prelude");
        assert!(tc.is_def_eq(&ty, &prop()), "forall goal must be a Prop, got {ty:?}");
        // The facet-aware entry point picks the same path up.
        let via_facets =
            elaborate_goal_typed_with_facets("forall i: u64, i + 0 == i", &[], &FacetTable::new())
                .expect("the facet-aware entry point must route quantified clauses");
        assert_eq!(goal, via_facets);
    }

    #[test]
    fn exists_goal_elaborates_and_typechecks_as_prop() {
        let env = Environment::with_prelude();
        let tc = TypeChecker::new(&env);
        for (spec, ty_name) in
            [("exists i: u64, i == 0", "u64"), ("exists n: nat, n + n == n", "nat")]
        {
            let goal = elaborate_goal_typed(spec, &[])
                .unwrap_or_else(|e| panic!("`{spec}` must elaborate: {e}"));
            let ty = tc
                .infer_type(&goal)
                .unwrap_or_else(|e| panic!("`{spec}` must be well-typed: {e:?}"));
            assert!(tc.is_def_eq(&ty, &prop()), "`{spec}` over {ty_name} must be a Prop");
            let dump = format!("{goal:?}");
            assert!(dump.contains("Exists"), "`{spec}` must elaborate through Exists: {dump}");
        }
    }

    #[test]
    fn implication_elaborates_and_typechecks_as_prop() {
        let env = Environment::with_prelude();
        let tc = TypeChecker::new(&env);
        let goal = elaborate_goal_typed("a <= b ==> a < b + 1", &[("a", "u64"), ("b", "u64")])
            .expect("an implication clause must elaborate");
        let ty = tc.infer_type(&goal).expect("implication goal must be well-typed");
        assert!(tc.is_def_eq(&ty, &prop()), "implication goal must be a Prop");
        // Right-associative chain: `A ==> B ==> C` is `A → (B → C)`.
        let chain =
            elaborate_goal_typed("a <= b ==> b <= a ==> a == b", &[("a", "nat"), ("b", "nat")])
                .expect("a right-associated implication chain must elaborate");
        let chain_ty = tc.infer_type(&chain).expect("chain goal must be well-typed");
        assert!(tc.is_def_eq(&chain_ty, &prop()), "chain goal must be a Prop");
    }

    #[test]
    fn quantifier_de_bruijn_indices_are_pinned() {
        // "forall i: u64, a <= i ==> a < i + 1" with the clause param `a : u64`.
        // Binder order outer→inner: [a (closed), i (quantifier), ==> hypothesis].
        // In the LHS (offset 0, vars [a, i]):  a = bvar 1, i = bvar 0.
        // In the RHS (offset 1, one arrow deeper): a = bvar 2, i = bvar 1.
        // This exact-term pin holds the offset arithmetic in place.
        let dom = Domain::Machine(MachineUIntWidth::U64);
        let lhs = dom.cmp("le", Expr::bvar(1), Expr::bvar(0));
        let rhs = dom.cmp(
            "lt",
            Expr::bvar(2),
            dom_bin(&dom, "add", Expr::bvar(1), dom.numeral(1).unwrap()),
        );
        let expected = Expr::pi(
            BinderInfo::Default,
            dom.ty(),
            Expr::pi(BinderInfo::Default, dom.ty(), Expr::pi(BinderInfo::Default, lhs, rhs)),
        );
        let goal = elaborate_goal_typed("forall i: u64, a <= i ==> a < i + 1", &[("a", "u64")])
            .expect("mixed free/bound clause must elaborate");
        assert_eq!(goal, expected, "de Bruijn indices drifted from the pinned encoding");
        // And the pinned term is genuinely kernel-well-typed, so the pin cannot
        // silently encode a nonsense statement.
        let env = Environment::with_prelude();
        let tc = TypeChecker::new(&env);
        let _ = tc.infer_type(&goal).expect("pinned goal must be well-typed");
    }

    #[test]
    fn forall_true_instance_reduces_definitionally() {
        // A TRUE closed instance of the elaborated body: instantiating
        // `forall i: nat, i + 0 == i` at `7` yields `Eq Nat (Nat.add 7 0) 7`,
        // whose sides are definitionally equal (ι-reduction of `Nat.add`).
        let env = Environment::with_prelude();
        let tc = TypeChecker::new(&env);
        let goal = elaborate_goal_typed("forall i: nat, i + 0 == i", &[])
            .expect("nat forall clause must elaborate");
        let ExprKind::Pi(_, binder_ty, body) = goal.kind() else {
            panic!("a forall clause must elaborate to a Pi, got {goal:?}");
        };
        assert_eq!(**binder_ty, nat(), "the binder must quantify over Nat");
        let seven = Expr::nat_lit(7);
        let instance = body.instantiate(&seven);
        // `Eq Nat (Nat.add 7 0) 7` — destructure the Eq applications and check
        // the sides definitionally.
        let ExprKind::App(eq_lhs, rhs) = instance.kind() else {
            panic!("instantiated body must be an Eq application: {instance:?}");
        };
        let ExprKind::App(_, lhs) = eq_lhs.kind() else {
            panic!("instantiated body must be a two-argument Eq: {instance:?}");
        };
        assert!(tc.is_def_eq(lhs, rhs), "`7 + 0` must reduce definitionally to `7`: {instance:?}");
        // The instantiated proposition is inhabited by `Eq.refl Nat 7` — the
        // kernel accepts the reflexivity proof AT the instance type, which is
        // the full "TRUE closed instance" check.
        let refl = Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]),
            [nat(), seven],
        );
        tc.check_type(&refl, &instance).expect("Eq.refl must inhabit the true instance");
    }

    #[test]
    fn wrong_domain_binder_fails_closed() {
        for spec in
            ["forall i: i256, i + 0 == i", "forall i: usize, i == i", "exists i: String, i == i"]
        {
            let err = elaborate_goal_typed(spec, &[])
                .expect_err("an unsupported binder type must fail closed");
            assert!(
                err.contains("unsupported quantifier binder type"),
                "`{spec}` must name the binder-type gate: {err}"
            );
        }
    }

    #[test]
    fn multi_binder_and_nested_quantifiers_fail_closed() {
        let err = elaborate_goal_typed("forall i: u64, j: u64, i + j == j + i", &[])
            .expect_err("a multi-binder head must fail closed");
        assert!(err.contains("multiple binders"), "{err}");
        let err = elaborate_goal_typed("forall i: u64, forall j: u64, i <= j", &[])
            .expect_err("a nested quantifier must fail closed");
        assert!(err.contains("head of a clause"), "{err}");
        let err = elaborate_goal_typed("x == x ==> forall i: u64, i <= i", &[("x", "u64")])
            .expect_err("a quantifier under an implication must fail closed");
        assert!(err.contains("head of a clause"), "{err}");
    }

    #[test]
    fn binder_shadowing_a_param_fails_closed() {
        // `i` is both a clause parameter and the quantifier binder: the binder
        // would capture the parameter's occurrences, so it fails closed. The
        // bijection gate reports the un-referenced parameter (`i` is bound, not
        // free) before elaboration is even attempted.
        let err = elaborate_goal_typed("forall i: u64, i + 0 == i", &[("i", "u64")])
            .expect_err("a binder shadowing a clause param must fail closed");
        assert!(
            err.contains("extra: [i]") || err.contains("shadows"),
            "shadowing must be rejected, got: {err}"
        );
        // With the param genuinely occurring free alongside the shadowing
        // binder, the same gate still refuses (the free occurrence set and the
        // binding set cannot form a bijection).
        let err = elaborate_goal_typed("a <= a ==> (forall a: u64, a <= a)", &[("a", "u64")])
            .expect_err("a shadowing binder alongside free occurrences must fail closed");
        assert!(!err.is_empty());
    }

    #[test]
    fn quantified_clause_bindings_stay_an_exact_bijection() {
        // The quantifier-bound variable needs NO entry in var_types…
        let _ = elaborate_goal_typed("forall i: u64, i <= n", &[("n", "u64")])
            .expect("free `n` + bound `i` with exactly `n` bound must elaborate");
        // …and the free variable still must have one.
        let err = elaborate_goal_typed("forall i: u64, i <= n", &[])
            .expect_err("missing free-variable binding must fail closed");
        assert!(err.contains("missing: [n]"), "{err}");
        // Extra bindings still fail closed.
        let err = elaborate_goal_typed("forall i: u64, i <= i", &[("ghost", "u64")])
            .expect_err("extra bindings must fail closed");
        assert!(err.contains("extra: [ghost]"), "{err}");
    }

    #[test]
    fn implication_with_calls_keeps_the_e6_facet_gate() {
        // The facet diagnostic walk reaches leaves under quantifiers and
        // implications: a program-function call still fails closed with the
        // E6 diagnostic, not a generic parse error.
        let err = elaborate_goal_typed_with_facets(
            "forall i: u64, f(i) <= i ==> i == 0",
            &[],
            &FacetTable::new(),
        )
        .expect_err("a call inside a quantified clause must fail closed");
        assert!(err.contains("E6"), "the E6 diagnostic must win: {err}");
    }

    #[test]
    fn admitted_call_elaborates_inside_a_quantifier_body() {
        // The E6 admission scope covers the quantified path: an ADMITTED call
        // in a quantifier body elaborates to its kernel constant, applied to
        // the quantifier-bound argument.
        let cert = || FacetStatus::Certified { evidence: "test".into() };
        let admissible =
            FnFacets { pure: cert(), total: cert(), deterministic: cert(), no_panic: cert() };
        let mut t = FacetTable::new();
        t.insert("wid", admissible);
        t.admit("wid", Admission { kernel_const: "wid".into(), arity: 1 });
        let goal = elaborate_goal_typed_with_facets("forall x: u64, wid(x) <= x", &[], &t)
            .expect("an admitted call under a quantifier must elaborate");
        assert!(format!("{goal:?}").contains("wid"), "{goal:?}");
    }

    #[test]
    fn plain_fragment_is_untouched_by_the_pre_parser() {
        // No quantifier keyword and no `==>`: the original path, byte-for-byte.
        let plain = elaborate_goal_typed("x + 0 == x", &[("x", "u64")]).unwrap();
        let dump = format!("{plain:?}");
        assert!(!dump.contains("Exists"), "{dump}");
        // Identifiers merely CONTAINING the keywords are not reserved.
        let _ = elaborate_goal_typed(
            "forall_count <= existsx",
            &[("forall_count", "u64"), ("existsx", "u64")],
        )
        .expect("keyword-prefixed identifiers must stay ordinary variables");
    }

    #[test]
    fn malformed_quantifier_spellings_fail_closed() {
        // Adversarial spellings around the pre-parser: every one must ERROR —
        // never silently elaborate to something else.
        for spec in [
            "forall",                            // keyword alone
            "forall , x == x",                   // missing binder name
            "forall 1x: u64, x == x",            // binder name starts with a digit
            "forall i u64, i == i",              // missing `:`
            "forall i: u64 i == i",              // missing `,`
            "forall i: , i == i",                // missing type
            "forall i: u64,",                    // empty body
            "==> x == x",                        // implication with empty LHS
            "x == x ==>",                        // implication with empty RHS
            "x == x ==> ==> x == x",             // doubled arrow
            "forall i j: u64, i <= j",           // design's multi-binder (future)
            "(forall i: u64, i <= n) && n == n", // quantifier under a connective
        ] {
            assert!(
                elaborate_goal_typed(spec, &[("x", "u64")]).is_err()
                    && elaborate_goal_typed(spec, &[]).is_err()
                    && elaborate_goal_typed(spec, &[("n", "u64")]).is_err(),
                "`{spec}` must fail closed under every binding set"
            );
        }
    }

    #[test]
    fn exact_quantifier_keywords_cannot_be_reintroduced_as_free_variables() {
        for keyword in ["forall", "exists"] {
            let binding = [(keyword, "u64")];
            let err = elaborate_goal_typed(keyword, &binding)
                .expect_err("an exact quantifier keyword must stay reserved");
            assert!(
                err.contains("expects a binder name"),
                "`{keyword}` must route through the quantifier parser: {err}"
            );

            let parenthesized = format!("({keyword})");
            let err = elaborate_goal_typed(&parenthesized, &binding)
                .expect_err("a parenthesized exact quantifier keyword must stay reserved");
            assert!(
                err.contains("expects a binder name"),
                "`{parenthesized}` must route through the quantifier parser: {err}"
            );
        }
    }

    #[test]
    fn true_and_false_implications_are_distinct_statements() {
        // `a <= b ==> a <= b` (true) and `a <= b ==> b <= a` (false) both
        // ELABORATE (elaboration is total over the fragment; proof is
        // gradual), but to distinct well-typed statements.
        let env = Environment::with_prelude();
        let tc = TypeChecker::new(&env);
        let t = elaborate_goal_typed("a <= b ==> a <= b", &[("a", "nat"), ("b", "nat")]).unwrap();
        let f = elaborate_goal_typed("a <= b ==> b <= a", &[("a", "nat"), ("b", "nat")]).unwrap();
        let _ = tc.infer_type(&t).expect("true implication well-typed");
        let _ = tc.infer_type(&f).expect("false implication well-typed");
        assert_ne!(t, f);
        // The `==>` encoding coincides with the contract path's `pre → post`
        // (the same Prop arrow), so a citation for one proves the other.
        let contract = elaborate_contract("a <= b", "a <= b").unwrap();
        // elaborate_contract collects vars from both clauses in order [a, b] —
        // identical statement shape.
        assert_eq!(t, contract, "`==>` and requires/ensures must build the same Prop arrow");
    }
}
