// trust-strengthen/abstract_domains/congruence.rs: Congruence domain
//
// Modular arithmetic domain: tracks (value mod stride) for each variable.
// Useful for alignment, shift-amount, and power-of-two properties.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;
use std::fmt;

use super::AbstractDomainOps;

// ---------------------------------------------------------------------------
// CongruenceValue
// ---------------------------------------------------------------------------

/// A congruence value: `value === residue (mod modulus)`.
///
/// Represents the set `{ residue + k * modulus | k in Z }`.
/// Special cases:
/// - `modulus == 0` means a singleton `{ residue }` (exact value).
/// - Top is represented by `modulus == 1, residue == 0` (any integer).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CongruenceValue {
    /// The empty set (unreachable).
    Bottom,
    /// A congruence class: `x === residue (mod modulus)`.
    /// Invariant: `0 <= residue < modulus` (or modulus == 0 for exact).
    Congruence { modulus: u64, residue: u64 },
}

impl CongruenceValue {
    /// Create a congruence value from a constant.
    #[must_use]
    pub fn constant(value: u64) -> Self {
        Self::Congruence { modulus: 0, residue: value }
    }

    /// Create a congruence class.
    #[must_use]
    pub fn new(modulus: u64, residue: u64) -> Self {
        if modulus == 0 {
            Self::Congruence { modulus: 0, residue }
        } else {
            Self::Congruence { modulus, residue: residue % modulus }
        }
    }

    /// Top: any value (modulus 1).
    #[must_use]
    pub fn top_value() -> Self {
        Self::Congruence { modulus: 1, residue: 0 }
    }

    /// Check if this value contains a specific integer.
    #[must_use]
    pub fn contains(&self, value: u64) -> bool {
        match self {
            Self::Bottom => false,
            Self::Congruence { modulus: 0, residue } => value == *residue,
            Self::Congruence { modulus, residue } => value % modulus == *residue,
        }
    }

    /// Returns true if this is the top element (any value).
    #[must_use]
    pub fn is_top(&self) -> bool {
        matches!(self, Self::Congruence { modulus: 1, residue: 0 })
    }

    /// Returns true if this is an exact constant.
    #[must_use]
    pub fn is_constant(&self) -> bool {
        matches!(self, Self::Congruence { modulus: 0, .. })
    }
}

impl fmt::Display for CongruenceValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Bottom => write!(f, "bottom"),
            Self::Congruence { modulus: 0, residue } => write!(f, "={residue}"),
            Self::Congruence { modulus: 1, residue: 0 } => write!(f, "top"),
            Self::Congruence { modulus, residue } => {
                write!(f, "{residue} (mod {modulus})")
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Helper functions
// ---------------------------------------------------------------------------

/// GCD helper.
pub(crate) fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}

/// Congruence addition.
fn congruence_add(a: CongruenceValue, b: CongruenceValue) -> CongruenceValue {
    match (a, b) {
        (CongruenceValue::Bottom, _) | (_, CongruenceValue::Bottom) => CongruenceValue::Bottom,
        (
            CongruenceValue::Congruence { modulus: ma, residue: ra },
            CongruenceValue::Congruence { modulus: mb, residue: rb },
        ) => {
            let m = if ma == 0 && mb == 0 {
                0
            } else if ma == 0 {
                mb
            } else if mb == 0 {
                ma
            } else {
                gcd(ma, mb)
            };
            let r = ra.wrapping_add(rb);
            if m == 0 {
                CongruenceValue::Congruence { modulus: 0, residue: r }
            } else {
                CongruenceValue::new(m, r % m)
            }
        }
    }
}

/// Congruence multiplication by constant.
fn congruence_mul_const(val: CongruenceValue, c: u64) -> CongruenceValue {
    match val {
        CongruenceValue::Bottom => CongruenceValue::Bottom,
        CongruenceValue::Congruence { modulus, residue } => {
            if c == 0 {
                return CongruenceValue::constant(0);
            }
            let new_modulus = modulus.saturating_mul(c);
            let new_residue = residue.wrapping_mul(c);
            if new_modulus == 0 {
                CongruenceValue::Congruence { modulus: 0, residue: new_residue }
            } else {
                CongruenceValue::new(new_modulus, new_residue % new_modulus)
            }
        }
    }
}

/// Congruence modulo by constant.
fn congruence_mod_const(val: CongruenceValue, c: u64) -> CongruenceValue {
    match val {
        CongruenceValue::Bottom => CongruenceValue::Bottom,
        CongruenceValue::Congruence { modulus, residue } => {
            if c == 0 {
                return CongruenceValue::Bottom; // Undefined
            }
            let new_modulus = if modulus == 0 {
                0 // Exact constant: result is exact
            } else {
                gcd(modulus, c)
            };
            let new_residue = residue % c;
            if new_modulus == 0 {
                CongruenceValue::Congruence { modulus: 0, residue: new_residue }
            } else {
                CongruenceValue::new(new_modulus, new_residue % new_modulus)
            }
        }
    }
}

/// Congruence right shift by constant.
fn congruence_shr_const(val: CongruenceValue, shift: u64) -> CongruenceValue {
    match val {
        CongruenceValue::Bottom => CongruenceValue::Bottom,
        CongruenceValue::Congruence { modulus, residue } => {
            if shift >= 64 {
                return CongruenceValue::constant(0);
            }
            let divisor = 1u64.checked_shl(shift as u32).unwrap_or(u64::MAX);
            let new_residue = residue >> shift;
            let new_modulus = if modulus == 0 {
                0
            } else if modulus % divisor == 0 {
                modulus / divisor
            } else {
                // Not evenly divisible -- lose precision
                1 // Top
            };
            if new_modulus == 0 {
                CongruenceValue::Congruence { modulus: 0, residue: new_residue }
            } else {
                CongruenceValue::new(new_modulus, new_residue)
            }
        }
    }
}

/// Join two congruence values.
pub(crate) fn congruence_join(a: CongruenceValue, b: CongruenceValue) -> CongruenceValue {
    match (a, b) {
        (CongruenceValue::Bottom, x) | (x, CongruenceValue::Bottom) => x,
        (
            CongruenceValue::Congruence { modulus: ma, residue: ra },
            CongruenceValue::Congruence { modulus: mb, residue: rb },
        ) => {
            // Join: gcd(ma, mb, |ra - rb|)
            let diff = ra.abs_diff(rb);
            let mut m = gcd(ma, mb);
            if diff > 0 {
                m = gcd(m, diff);
            }
            if m == 0 && ra == rb {
                CongruenceValue::Congruence { modulus: 0, residue: ra }
            } else if m == 0 {
                // Different exact values: modulus = diff
                CongruenceValue::new(diff, ra.min(rb) % diff)
            } else {
                CongruenceValue::new(m, ra % m)
            }
        }
    }
}

/// Meet two congruence values.
pub(crate) fn congruence_meet(a: CongruenceValue, b: CongruenceValue) -> CongruenceValue {
    match (a, b) {
        (CongruenceValue::Bottom, _) | (_, CongruenceValue::Bottom) => CongruenceValue::Bottom,
        (
            CongruenceValue::Congruence { modulus: ma, residue: ra },
            CongruenceValue::Congruence { modulus: mb, residue: rb },
        ) => {
            if ma == 1 && ra == 0 {
                return b; // a is top
            }
            if mb == 1 && rb == 0 {
                return a; // b is top
            }
            if ma == 0 && mb == 0 {
                // Both exact: must agree
                if ra == rb { CongruenceValue::constant(ra) } else { CongruenceValue::Bottom }
            } else if ma == 0 {
                // a is exact, b is congruence: check if a satisfies b
                if rb == 0 || ra % mb == rb {
                    CongruenceValue::constant(ra)
                } else {
                    CongruenceValue::Bottom
                }
            } else if mb == 0 {
                // b is exact, a is congruence: check if b satisfies a
                if ra == 0 || rb % ma == ra {
                    CongruenceValue::constant(rb)
                } else {
                    CongruenceValue::Bottom
                }
            } else {
                // Both congruences: use CRT-like approach
                // Result modulus = lcm(ma, mb) if residues are compatible
                let g = gcd(ma, mb);
                let diff = ra.abs_diff(rb);
                if diff % g != 0 {
                    CongruenceValue::Bottom // Incompatible
                } else {
                    let lcm = (ma / g).saturating_mul(mb);
                    // The residue mod lcm: pick ra (it satisfies both if compatible)
                    CongruenceValue::new(lcm, ra % lcm)
                }
            }
        }
    }
}

/// Check if `a` is a subset of `b` in the congruence lattice.
pub(crate) fn congruence_subset(a: CongruenceValue, b: CongruenceValue) -> bool {
    match (a, b) {
        (CongruenceValue::Bottom, _) => true,
        (_, CongruenceValue::Bottom) => false,
        (_, CongruenceValue::Congruence { modulus: 1, residue: 0 }) => true, // b is top
        (CongruenceValue::Congruence { modulus: 1, residue: 0 }, _) => false, // a is top, b isn't
        (
            CongruenceValue::Congruence { modulus: ma, residue: ra },
            CongruenceValue::Congruence { modulus: mb, residue: rb },
        ) => {
            if mb == 0 {
                // b is exact: a must also be exact and equal
                ma == 0 && ra == rb
            } else if ma == 0 {
                // a is exact: check if it satisfies b's congruence
                ra % mb == rb
            } else {
                // a's modulus must be a multiple of b's modulus
                // and residues must agree mod b's modulus
                ma % mb == 0 && ra % mb == rb
            }
        }
    }
}

// ---------------------------------------------------------------------------
// CongruenceDomain
// ---------------------------------------------------------------------------

/// Congruence domain: tracks `(value mod stride)` for each variable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CongruenceDomain {
    /// Per-variable congruence information.
    pub(super) vars: BTreeMap<String, CongruenceValue>,
    /// Whether this is the bottom element.
    pub(super) is_bottom: bool,
}

impl CongruenceDomain {
    /// Create a top (unconstrained) congruence domain.
    #[must_use]
    pub fn new() -> Self {
        Self { vars: BTreeMap::new(), is_bottom: false }
    }

    /// Create a bottom domain.
    #[must_use]
    pub fn new_bottom() -> Self {
        Self { vars: BTreeMap::new(), is_bottom: true }
    }

    /// Set a variable to a specific congruence.
    pub fn set_var(&mut self, var: impl Into<String>, value: CongruenceValue) {
        if self.is_bottom {
            return;
        }
        if matches!(value, CongruenceValue::Bottom) {
            self.is_bottom = true;
            return;
        }
        self.vars.insert(var.into(), value);
    }

    /// Get the congruence value of a variable.
    #[must_use]
    pub fn get_var(&self, var: &str) -> CongruenceValue {
        if self.is_bottom {
            return CongruenceValue::Bottom;
        }
        self.vars.get(var).copied().unwrap_or(CongruenceValue::top_value())
    }

    /// Transfer: `dst = src_a + src_b`.
    ///
    /// If `a === r_a (mod m_a)` and `b === r_b (mod m_b)`, then
    /// `a + b === (r_a + r_b) (mod gcd(m_a, m_b))`.
    pub fn transfer_add(&mut self, dst: &str, src_a: &str, src_b: &str) {
        if self.is_bottom {
            return;
        }
        let a = self.get_var(src_a);
        let b = self.get_var(src_b);
        let result = congruence_add(a, b);
        self.set_var(dst, result);
    }

    /// Transfer: `dst = src * constant`.
    ///
    /// If `src === r (mod m)`, then `src * c === (r * c) (mod m * c)`.
    pub fn transfer_mul_const(&mut self, dst: &str, src: &str, constant: u64) {
        if self.is_bottom {
            return;
        }
        let val = self.get_var(src);
        let result = congruence_mul_const(val, constant);
        self.set_var(dst, result);
    }

    /// Transfer: `dst = src % constant`.
    ///
    /// If `src === r (mod m)`, then `src % c === r % c (mod gcd(m, c))`.
    pub fn transfer_mod_const(&mut self, dst: &str, src: &str, constant: u64) {
        if self.is_bottom || constant == 0 {
            return;
        }
        let val = self.get_var(src);
        let result = congruence_mod_const(val, constant);
        self.set_var(dst, result);
    }

    /// Transfer: `dst = src >> constant` (logical right shift).
    ///
    /// Right shift by `c` divides the modulus: if `src === r (mod m)` and
    /// `m` is divisible by `2^c`, then `src >> c === (r >> c) (mod m >> c)`.
    pub fn transfer_shr_const(&mut self, dst: &str, src: &str, shift: u64) {
        if self.is_bottom {
            return;
        }
        let val = self.get_var(src);
        let result = congruence_shr_const(val, shift);
        self.set_var(dst, result);
    }

    /// Check if a variable's value is known to be less than a bound.
    ///
    /// Only works for exact constants (modulus == 0).
    #[must_use]
    pub fn check_less_than(&self, var: &str, bound: u64) -> bool {
        match self.get_var(var) {
            CongruenceValue::Congruence { modulus: 0, residue } => residue < bound,
            _ => false,
        }
    }
}

impl Default for CongruenceDomain {
    fn default() -> Self {
        Self::new()
    }
}

impl fmt::Display for CongruenceDomain {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_bottom {
            return write!(f, "bottom");
        }
        if self.vars.is_empty() {
            return write!(f, "top");
        }
        let parts: Vec<String> = self.vars.iter().map(|(k, v)| format!("{k}: {v}")).collect();
        write!(f, "cong({})", parts.join(", "))
    }
}

impl AbstractDomainOps for CongruenceDomain {
    fn join(&self, other: &Self) -> Self {
        if self.is_bottom {
            return other.clone();
        }
        if other.is_bottom {
            return self.clone();
        }
        let mut result = Self::new();
        // Union of variable sets
        let all_vars: std::collections::BTreeSet<&String> =
            self.vars.keys().chain(other.vars.keys()).collect();
        for var in all_vars {
            let a = self.get_var(var);
            let b = other.get_var(var);
            let joined = congruence_join(a, b);
            if !joined.is_top() {
                result.vars.insert(var.clone(), joined);
            }
        }
        result
    }

    fn meet(&self, other: &Self) -> Self {
        if self.is_bottom || other.is_bottom {
            return Self::new_bottom();
        }
        let mut result = Self::new();
        let all_vars: std::collections::BTreeSet<&String> =
            self.vars.keys().chain(other.vars.keys()).collect();
        for var in all_vars {
            let a = self.get_var(var);
            let b = other.get_var(var);
            let met = congruence_meet(a, b);
            if matches!(met, CongruenceValue::Bottom) {
                return Self::new_bottom();
            }
            if !met.is_top() {
                result.vars.insert(var.clone(), met);
            }
        }
        result
    }

    fn widen(&self, new: &Self) -> Self {
        // For congruence domain, widening = join (already terminates due to
        // finite lattice height -- modulus chain is bounded by values seen).
        self.join(new)
    }

    fn narrow(&self, new: &Self) -> Self {
        // Narrowing = meet for congruence (finite lattice).
        self.meet(new)
    }

    fn is_bottom(&self) -> bool {
        self.is_bottom
    }

    fn is_top(&self) -> bool {
        !self.is_bottom && self.vars.is_empty()
    }

    fn bottom() -> Self {
        Self::new_bottom()
    }

    fn top() -> Self {
        Self::new()
    }

    fn is_subset_of(&self, other: &Self) -> bool {
        if self.is_bottom {
            return true;
        }
        if other.is_bottom {
            return false;
        }
        // For each variable in other, check that self's congruence is more precise
        for (var, other_val) in &other.vars {
            let self_val = self.get_var(var);
            if !congruence_subset(self_val, *other_val) {
                return false;
            }
        }
        true
    }
}
