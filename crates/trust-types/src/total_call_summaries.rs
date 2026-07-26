//! Facts about modeled total core/std call summaries that more than one
//! pipeline stage must agree on.
//!
//! The TrustIr bridge models certain total calls as fresh-symbolic results and
//! attaches known postcondition facts (e.g. `len() <= isize::MAX`). The VC
//! formula lane must attach the SAME facts to the SAME calls, or obligations
//! discharged via the formula path see an unconstrained result and false-FAIL
//! safe code (observed: `s.len() + 1`, build #30). Keeping the matcher here —
//! the shared dependency of trust-ir-bridge and trust-vcgen — makes the two
//! artifacts impossible to drift apart.

/// Canonical wire name for compiler-authenticated, pinned-total std primitive
/// comparison calls. The extractor rewrites only a resolved comparison whose
/// defining crate, diagnostic trait, method, and primitive `Self` type are all
/// authenticated by rustc; source-spellable derived attributes and generic
/// container traits carry no authority.
///
/// The legacy `CLONE` identifier and `__trust_total_clone` bytes are retained for
/// dump compatibility. They no longer authorize derived `Clone`, keyed
/// collection, hashing, or ordering summaries.
pub const TRUST_TOTAL_CLONE_SENTINEL: &str = "__trust_total_clone";

/// True for `str`/`String`/`Vec`/slice `len()` calls, whose result is bounded
/// by `isize::MAX` (no Rust allocation exceeds `isize::MAX` bytes, so no
/// element count does either — a language-level safety invariant, never
/// vacuous).
#[must_use]
pub fn total_summary_len_bound(callee: &str) -> bool {
    if callee.starts_with("__trust_crate@") || !callee.ends_with("::len") {
        return false;
    }
    [
        "core::str::",
        "alloc::str::",
        "std::str::",
        "core::slice::",
        "alloc::slice::",
        "std::slice::",
        "alloc::string::String",
        "std::string::String",
        "alloc::vec::Vec",
        "std::vec::Vec",
    ]
    .iter()
    .any(|root| canonical_plain_trait_method(callee, root, "len"))
}

/// True for the std value-preserving INTEGER conversions `<intT as From<intS>>::from(x)`
/// and `intS::into::<intT>()`. `From`/`Into` between integer types is implemented ONLY for
/// lossless (widening or same-width) conversions, so the result equals the corresponding
/// `as`-cast of the argument — `zext` (unsigned source) / `sext` (signed source) /
/// `bitcast` (same width) — and the call cannot panic. The TrustIr bridge confirms the
/// argument and destination are integers with `dst_width >= src_width` (declining the
/// signed->unsigned direction `From` never provides), then lowers the call AS that cast —
/// no body, no obligation — instead of failing to resolve the (body-less, unavailable) std
/// `from`/`into`. Without this, a verified function dies at its first `u32::from(byte)`.
///
/// This is the first entry of the Trust Std summary registry — the single source of truth
/// shared by the bridge and the VC formula lane (so the two cannot drift). The fact is a
/// THEOREM of `From<int>` (value-preservation), not an asserted axiom; see
/// `docs/design/trust-std-design.md`.
#[must_use]
pub fn is_value_preserving_int_convert_call(callee: &str) -> bool {
    if callee.starts_with("__trust_crate@") {
        return false;
    }
    [
        ("core::convert::From", "from"),
        ("std::convert::From", "from"),
        ("core::convert::Into", "into"),
        ("std::convert::Into", "into"),
    ]
    .iter()
    .any(|(trait_path, method)| canonical_plain_trait_method(callee, trait_path, method))
}

fn canonical_plain_trait_method(callee: &str, trait_path: &str, method: &str) -> bool {
    let Some(rest) = callee.strip_prefix(trait_path) else { return false };
    if rest == format!("::{method}") {
        return true;
    }
    let generic = rest.strip_prefix("::").unwrap_or(rest);
    let Some(generic) = generic.strip_prefix('<') else { return false };
    let mut depth = 1usize;
    for (index, byte) in generic.bytes().enumerate() {
        match byte {
            b'<' => depth += 1,
            b'>' => {
                depth -= 1;
                if depth == 0 {
                    return &generic[index + 1..] == format!("::{method}");
                }
            }
            _ => {}
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn len_summary_requires_an_unambiguous_standard_root() {
        for callee in [
            "core::str::<impl str>::len",
            "alloc::string::String::len",
            "alloc::vec::Vec::<u8>::len",
            "core::slice::<impl [u8]>::len",
        ] {
            assert!(total_summary_len_bound(callee), "expected canonical len: {callee}");
        }
        for callee in [
            "mycrate::String::len",
            "mycrate::core::slice::Iter::len",
            "__trust_crate@deadbeef::std::vec::Vec::<u8>::len",
            "alloc::string::StringEvil::len",
            "std::vec::VecEvil::<u8>::len",
            "core::str::evil::len",
            "core::slice::Iter::<u8>::len",
        ] {
            assert!(!total_summary_len_bound(callee), "must fail closed: {callee}");
        }
    }

    #[test]
    fn integer_conversion_summary_requires_a_canonical_trait_path() {
        for callee in [
            "core::convert::From::from",
            "std::convert::Into::into",
            "core::convert::From<u8>::from",
            "std::convert::Into::<u64>::into",
        ] {
            assert!(
                is_value_preserving_int_convert_call(callee),
                "expected canonical conversion: {callee}"
            );
        }
        for callee in [
            "mycrate::convert::From::from",
            "mycrate::core::convert::Into::into",
            "__trust_crate@deadbeef::std::convert::From::from",
            "core::convert::FromEvil::from",
        ] {
            assert!(!is_value_preserving_int_convert_call(callee), "must fail closed: {callee}");
        }
    }
}
