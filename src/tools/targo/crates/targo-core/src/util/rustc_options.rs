//! Trust: Trust-authored, no upstream counterpart. Cargo passes `-C`/`-Z`
//! options through as opaque strings and never has to agree with rustc about
//! what one *means*. Trust's flag policy does, so every comparison in the
//! frontend goes through this module — matching a literal spelling instead
//! would let an equivalent one walk past the check — rustc treats every `-`/`_`
//! mixture of a key as the same option, and when a key repeats it honours the
//! last occurrence rather than the first.

use std::borrow::Cow;

/// Split a rustc `-C`/`-Z` option and canonicalize its key exactly as rustc's
/// option table does. rustc accepts every mixture of `-` and `_` in a key by
/// replacing dashes with underscores before lookup; security policy must use
/// the same equivalence relation or an alternate spelling can bypass it.
pub(crate) fn rustc_option_parts(option: &str) -> (Cow<'_, str>, Option<&str>) {
    let (name, value) = option
        .split_once('=')
        .map_or((option, None), |(name, value)| (name, Some(value)));
    let name = if name.contains('-') {
        Cow::Owned(name.replace('-', "_"))
    } else {
        Cow::Borrowed(name)
    };
    (name, value)
}

/// Match trustc's built-in backend alias before any policy comparison.
pub(crate) fn canonical_codegen_backend_value(value: &str) -> &str {
    if value == "trust_cg" {
        "trust-cg"
    } else {
        value
    }
}

#[cfg(test)]
mod tests {
    use super::{canonical_codegen_backend_value, rustc_option_parts};

    #[test]
    fn option_keys_match_rustc_dash_underscore_equivalence() {
        for spelling in [
            "trust-verify-session=proof",
            "trust_verify_session=proof",
            "trust-verify_session=proof",
            "trust_verify-session=proof",
        ] {
            let (name, value) = rustc_option_parts(spelling);
            assert_eq!(name, "trust_verify_session", "{spelling}");
            assert_eq!(value, Some("proof"), "{spelling}");
        }

        let (name, value) = rustc_option_parts("trust-verify=off");
        assert_eq!(name, "trust_verify");
        assert_eq!(value, Some("off"));
    }

    #[test]
    fn trust_cg_backend_alias_matches_the_compiler() {
        assert_eq!(canonical_codegen_backend_value("trust_cg"), "trust-cg");
        assert_eq!(canonical_codegen_backend_value("trust-cg"), "trust-cg");
        assert_eq!(canonical_codegen_backend_value("llvm"), "llvm");
    }
}
