//! Facts about modeled total core/std call summaries that more than one
//! pipeline stage must agree on.
//!
//! The TrustIr bridge models certain total calls as fresh-symbolic results and
//! attaches known postcondition facts (e.g. a nonnegative `len()`, plus
//! `len() <= isize::MAX` when the byte-size invariant proves it). The VC
//! formula lane must attach the SAME facts to the SAME calls, or obligations
//! discharged via the formula path see an unconstrained result and false-FAIL
//! safe code (observed: `s.len() + 1`, build #30). Keeping the matcher here —
//! the shared dependency of trust-ir-bridge and trust-vcgen — makes the two
//! artifacts impossible to drift apart.

/// Canonical wire name for a call the extractor proved TOTAL from compiler-
/// authenticated facts (`trust_mir_extract::convert::apply_total_clone_sentinel`):
/// a pinned-total std primitive comparison (defining crate, diagnostic trait,
/// method and primitive `Self` all authenticated by rustc), or a `Clone::clone`
/// whose trait is the real `Clone` lang item and whose receiver clone tree
/// `tcx_clone_is_total` proves total (a local impl only via `is_builtin_derived`,
/// i.e. rustc builtin-macro provenance), among the other arms that function
/// documents. A source-spellable `#[automatically_derived]` attribute carries no
/// authority (retired 2026-07-24).
pub const TRUST_TOTAL_CLONE_SENTINEL: &str = "__trust_total_clone";

/// True for canonical `str`/`String`/`Vec`/slice `len()` calls.
///
/// This is a call-identity predicate, not an upper-bound theorem: a slice or
/// `Vec` of a zero-sized type can have a length greater than `isize::MAX`.
/// Consumers that only need to identify the collection operation (for example,
/// to tie its result to an abstract collection length) should use this matcher.
#[must_use]
pub fn total_summary_len_call(callee: &str) -> bool {
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

/// True when the callee name alone proves that `len() <= isize::MAX`.
///
/// `str` and `String` lengths count bytes, so the allocation/object-size limit
/// supplies the bound without inspecting a receiver type. Slice lengths need a
/// separate non-ZST receiver check; `Vec<T>` is intentionally excluded because
/// the current verifier type can erase `T`, making `Vec<()>` indistinguishable
/// from a non-ZST vector at this boundary.
#[must_use]
pub fn total_summary_len_bound(callee: &str) -> bool {
    if callee.starts_with("__trust_crate@") || !callee.ends_with("::len") {
        return false;
    }
    ["core::str::", "alloc::str::", "std::str::", "alloc::string::String", "std::string::String"]
        .iter()
        .any(|root| canonical_plain_trait_method(callee, root, "len"))
}

/// True for a canonical slice `len()` call. Its result has the
/// `isize::MAX` upper bound only when the caller additionally proves that the
/// receiver's element type is non-zero-sized.
#[must_use]
pub fn total_summary_slice_len_call(callee: &str) -> bool {
    if callee.starts_with("__trust_crate@") || !callee.ends_with("::len") {
        return false;
    }
    ["core::slice::", "alloc::slice::", "std::slice::"]
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
    if rest.strip_prefix("::") == Some(method) {
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
                    return generic[index + 1..].strip_prefix("::") == Some(method);
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
    fn len_call_requires_an_unambiguous_standard_root() {
        for callee in [
            "core::str::<impl str>::len",
            "alloc::string::String::len",
            "alloc::vec::Vec::<u8>::len",
            "core::slice::<impl [u8]>::len",
        ] {
            assert!(total_summary_len_call(callee), "expected canonical len: {callee}");
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
            assert!(!total_summary_len_call(callee), "must fail closed: {callee}");
        }
    }

    #[test]
    fn name_only_len_bound_excludes_zst_capable_collections() {
        for callee in ["core::str::<impl str>::len", "alloc::string::String::len"] {
            assert!(total_summary_len_bound(callee), "byte length is bounded: {callee}");
        }
        for callee in [
            "alloc::vec::Vec::<u8>::len",
            "core::slice::<impl [u8]>::len",
            "core::slice::<impl [()]>::len",
        ] {
            assert!(
                !total_summary_len_bound(callee),
                "the name alone cannot exclude a ZST receiver: {callee}"
            );
        }
        assert!(total_summary_slice_len_call("core::slice::<impl [u8]>::len"));
        assert!(!total_summary_slice_len_call("core::slice::Iter::<u8>::len"));
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
