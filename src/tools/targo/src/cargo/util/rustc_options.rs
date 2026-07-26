//! Trust: Trust-authored, no upstream counterpart. Cargo passes `-C`/`-Z`
//! options through as opaque strings and never has to agree with rustc about
//! what one *means*. Trust's flag policy does, so every comparison in the
//! frontend goes through this module — matching a literal spelling instead
//! would let an equivalent one walk past the check — rustc treats every `-`/`_`
//! mixture of a key as the same option, and when a key repeats it honours the
//! last occurrence rather than the first.

use std::borrow::Cow;
use std::ffi::OsStr;

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

/// Decode the two ambient rustflag transports with Cargo's precedence and
/// token boundaries. The versioned encoded channel wins even when it is
/// empty; plain flags use Cargo's literal-space protocol rather than shell
/// parsing.
pub(crate) fn parse_rustflags_os(
    encoded: Option<&OsStr>,
    plain: Option<&OsStr>,
) -> Result<Vec<String>, String> {
    if let Some(encoded) = encoded {
        let encoded = encoded
            .to_str()
            .ok_or_else(|| "CARGO_ENCODED_RUSTFLAGS is not valid Unicode".to_string())?;
        return Ok(if encoded.is_empty() {
            Vec::new()
        } else {
            encoded.split('\x1f').map(str::to_string).collect()
        });
    }
    if let Some(plain) = plain {
        let plain = plain
            .to_str()
            .ok_or_else(|| "RUSTFLAGS is not valid Unicode".to_string())?;
        return Ok(plain
            .split(' ')
            .map(str::trim)
            .filter(|flag| !flag.is_empty())
            .map(str::to_string)
            .collect());
    }
    Ok(Vec::new())
}

#[cfg(test)]
mod tests {
    use std::ffi::OsStr;

    use super::{canonical_codegen_backend_value, parse_rustflags_os, rustc_option_parts};

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
    fn encoded_rustflags_win_and_preserve_empty_argument_boundaries() {
        assert_eq!(
            parse_rustflags_os(
                Some(OsStr::new("-Zfoo\x1f\x1fbar\x1f")),
                Some(OsStr::new("ignored plain")),
            ),
            Ok(vec!["-Zfoo".into(), "".into(), "bar".into(), "".into()])
        );
        assert_eq!(
            parse_rustflags_os(None, Some(OsStr::new("-Z foo\tbar  -C opt-level=2"))),
            Ok(vec![
                "-Z".into(),
                "foo\tbar".into(),
                "-C".into(),
                "opt-level=2".into()
            ])
        );
    }

    #[test]
    fn trust_cg_backend_alias_matches_the_compiler() {
        assert_eq!(canonical_codegen_backend_value("trust_cg"), "trust-cg");
        assert_eq!(canonical_codegen_backend_value("trust-cg"), "trust-cg");
        assert_eq!(canonical_codegen_backend_value("llvm"), "llvm");
    }
}
