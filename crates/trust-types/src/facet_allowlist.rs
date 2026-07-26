//! External E6 facet summaries.
//!
//! This is an authority boundary, not a diagnostic name matcher.  The current
//! [`Terminator::Call`](crate::Terminator::Call) model carries only a printable
//! callee path; it does not carry the rustc `DefId`/`Instance`, monomorphized
//! signature, or argument/result types needed to prove that a call denotes a
//! particular primitive operation.  Consequently the authority allowlist is
//! deliberately EMPTY.  A suffix such as `wrapping_add` or `::len` is never
//! evidence: user code can use the same suffix, and even generic `core`
//! functions can invoke arbitrary trait or drop glue.
//!
//! Entries may be reintroduced only after call extraction carries a stable,
//! exact instance identity and a validated closed signature.  Until then every
//! external call fails closed for every facet.

use std::collections::HashSet;

/// The four E6 facets.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Facet {
    Total,
    NoPanic,
    Pure,
    Deterministic,
}

/// Whether an external callee is an authority-grade known satisfier of `facet`.
///
/// Always false until the call IR carries exact rustc instance and signature
/// identity.  The arguments remain part of the API so callers cannot silently
/// fall back to their own string matching while the quarantine is active.
#[must_use]
pub fn is_known(_facet: Facet, _callee: &str) -> bool {
    false
}

/// Select authority-grade trusted externals for a facet.
///
/// The result is intentionally empty; see [`is_known`].
#[must_use]
pub fn trusted_external_for<I, S>(_facet: Facet, external_callees: I) -> HashSet<String>
where
    I: IntoIterator<Item = S>,
    S: Into<String>,
{
    // Consume the iterator so callers with a lazy extraction pipeline retain
    // their established evaluation behavior, but mint no trust from its text.
    for callee in external_callees {
        let _: String = callee.into();
    }
    HashSet::new()
}

#[cfg(test)]
mod tests {
    use super::*;

    const FACETS: [Facet; 4] = [Facet::Total, Facet::NoPanic, Facet::Pure, Facet::Deterministic];

    #[test]
    fn textual_external_names_never_confer_authority() {
        let suspicious = [
            "core::num::<impl u64>::wrapping_add",
            "core::num::<impl u64>::wrapping_div",
            "core::cmp::min",
            "core::cmp::Ord::clamp",
            "core::option::Option::<T>::unwrap_or_default",
            "evil::wrapping_add",
            "user::len",
        ];

        for facet in FACETS {
            for callee in suspicious {
                assert!(!is_known(facet, callee), "{callee} must not confer {facet:?}");
            }
        }
    }

    #[test]
    fn trusted_external_set_is_empty_for_every_facet() {
        let candidates =
            ["core::num::<impl u64>::wrapping_add".to_string(), "evil::wrapping_add".to_string()];
        for facet in FACETS {
            assert!(trusted_external_for(facet, candidates.clone()).is_empty());
        }
    }
}
