//! The FragmentEscape boundary: a typed, fail-closed diagnostic for any construct
//! outside the admitted deterministic integer fragment. Escape is NEVER a silent
//! drop — a partial `VerifiableFunction` could vacuously "prove" a truncated
//! program — so elaboration/lowering returns `Result<_, FragmentEscape>` and any
//! escape aborts the whole function's embedding.

use serde::{Deserialize, Serialize};
use thiserror::Error;

/// A construct the embedding refused, with enough context for the driving agent to
/// rewrite the TS, widen a gate, or split the function.
#[derive(Debug, Clone, Error, Serialize, Deserialize)]
#[error("TypeScript fragment escape in `{symbol}`: {reason:?}")]
pub struct FragmentEscape {
    /// The function/symbol being embedded when the escape occurred.
    pub symbol: String,
    /// The machine-classifiable reason.
    pub reason: UnsupportedTsConstruct,
}

impl FragmentEscape {
    #[must_use]
    pub fn new(symbol: impl Into<String>, reason: UnsupportedTsConstruct) -> Self {
        Self { symbol: symbol.into(), reason }
    }

    #[must_use]
    pub fn no_return(symbol: impl Into<String>) -> Self {
        Self::new(symbol, UnsupportedTsConstruct::MissingReturn)
    }

    #[must_use]
    pub fn unbound_var(symbol: impl Into<String>, var: impl Into<String>) -> Self {
        Self::new(symbol, UnsupportedTsConstruct::UnboundVariable { var: var.into() })
    }
}

/// The closed-world classification of what the fragment does not admit.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
#[non_exhaustive]
pub enum UnsupportedTsConstruct {
    /// A function body that does not end in an explicit `return`.
    MissingReturn,
    /// A variable referenced before binding (or outside the declared params/locals).
    UnboundVariable { var: String },
    /// A `number` whose interval could not be bounded to an integer width.
    UnboundedNumber { var: String },
    /// float / ToInt32 / bitwise-on-double semantics, or any non-integer arithmetic.
    NonIntegerArithmetic { detail: String },
    /// A call other than the inlinable `Math.min`/`Math.max` intrinsics.
    UnmodeledCall { callee: String },
    /// loops, try/catch, throw, async, generators, closures.
    UnsupportedControlFlow { kind: String },
    /// any AST/IR node the lowering has no arm for — the catch-all.
    UnknownConstruct { detail: String },
}
