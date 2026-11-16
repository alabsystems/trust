//! Trust (ARGS-FINGERPRINT-READ-1, 2026-10-07): the duplicate-crate-name
//! generic-argument fingerprint `::<__trust_args@HEX>` — its one grammar, and
//! the one helper every consumer that reads a callee's OWN generic arguments
//! uses to see past it.
//!
//! # What it is
//!
//! `trust_mir_extract::convert::direct_call_def_path` (DROP-NAME-COLLIDE-1)
//! appends a fingerprint of a call's full generic argument vector to a generic
//! callee path when the argument DISPLAY is not a crate identity: some def the
//! arguments name lives in a crate whose rendered name does not identify it — a
//! non-local crate whose NAME another crate of the graph shares (two semver
//! versions of one dependency), or a crate that wears a sysroot name without
//! being the compiler's own. That is the rule that stamps a callee ROOT
//! `__trust_crate@…`; the display printer does not stamp types INSIDE the
//! arguments, so two argument vectors whose text is identical (`shared::T` from
//! either crate) are told apart only by this tag. The producer,
//! `disambiguate_generic_call_path`, writes exactly
//! `format!("{path}::<__trust_args@{lo:016x}{hi:016x}>")`.
//!
//! (ARGS-FINGERPRINT-READ-1 round 2, 2026-10-07: until then the tag was written
//! on EVERY generic callee of a graph that merely contained a duplicate name, so
//! it said nothing about the arguments it followed.)
//!
//! # What a reader may do with it
//!
//! The group is an IDENTITY tag, not a generic argument: it is spelled as a
//! trailing turbofish only so that string keys stay distinct. A consumer that
//! reads "the method's own generic arguments" as the LAST `::<…>` group reads the
//! tag instead.
//!
//! * A reader of a VALUE in the arguments — a const literal (`as_chunks::<4>`),
//!   a primitive type (`f64`, `char`, `&str`) — may see past it with
//!   [`strip_trailing_args_fingerprint`]: no crate can spell those.
//! * A reader that compares a TYPE PATH in the arguments
//!   (`core::ops::range::RangeFull`, `core::num::wrapping::Wrapping<`) must
//!   DECLINE when [`args_display_may_name_a_same_named_crate`] holds. MEASURED
//!   (review of round 1): a crate built `--crate-name core` exporting
//!   `ops::range::RangeFull` with `start_bound = Included(&1000)` rendered
//!   `alloc::vec::Vec::<u32>::drain::<core::ops::range::RangeFull>::<__trust_args@…>`,
//!   and a reader that stripped the tag granted the cannot-panic carve-out to a
//!   `drain` that panics.
//! * A consumer that uses the callee path as a KEY (bundle lookup, call-key
//!   ledgers, def-path pins) or as a call IDENTITY (the termination lane's self
//!   call) keeps the tag: that is its whole purpose.

/// The literal opener of the fingerprint group, byte-for-byte as the producer
/// writes it.
pub const TRUST_ARGS_FINGERPRINT_PREFIX: &str = "::<__trust_args@";

/// `Fingerprint::split()` gives two `u64` halves, each rendered `{:016x}`. The
/// FIXED width is the producer's own injectivity argument.
pub const TRUST_ARGS_FINGERPRINT_HEX_LEN: usize = 32;

/// `"::<__trust_args@" + 32 hex + ">"`: a constant, so the group is located by
/// arithmetic from the END of the string, never by searching its text.
const TRUST_ARGS_FINGERPRINT_LEN: usize =
    TRUST_ARGS_FINGERPRINT_PREFIX.len() + TRUST_ARGS_FINGERPRINT_HEX_LEN + 1;

/// Render the fingerprint group for the two halves of a `Fingerprint` — the
/// spelling `disambiguate_generic_call_path` writes. Consumers' tests build
/// their fixtures with it so producer and readers cannot drift apart.
#[must_use]
pub fn render_trailing_args_fingerprint(lo: u64, hi: u64) -> String {
    format!("{TRUST_ARGS_FINGERPRINT_PREFIX}{lo:016x}{hi:016x}>")
}

/// `callee` with ONE trailing duplicate-crate-name argument fingerprint
/// removed, or `callee` unchanged when it carries none.
///
/// For readers of a VALUE in the arguments (a const literal, a primitive type)
/// only. A reader that compares a TYPE PATH must decline on a tagged callee
/// instead ([`args_display_may_name_a_same_named_crate`]): the tag is exactly
/// the producer's statement that those paths may name a same-named crate.
///
/// # The grammar, and why it cannot over-match
///
/// The ONLY accepted suffix is exactly
/// `"::<__trust_args@" <32 lowercase hex digits> ">"`, anchored at the END of
/// the string at a fixed offset. A `__trust_args`-looking fragment anywhere
/// else in the path is invisible to this function. `@` is not an identifier
/// character, so source cannot spell the suffix: a user type NAMED
/// `__trust_args` renders `f::<__trust_args>` (no `@`, no hex) and is kept. A
/// wrong hex length, an uppercase digit or a missing `>` keeps the whole path,
/// so a caller then declines exactly as it would on any unrecognized spelling.
/// The head must be non-empty: the tag is a suffix of a real call path.
///
/// The caller decides about whitespace: the producer writes no trailing space,
/// and this function does not trim.
#[must_use]
pub fn strip_trailing_args_fingerprint(callee: &str) -> &str {
    let Some(head_len) = callee.len().checked_sub(TRUST_ARGS_FINGERPRINT_LEN) else {
        return callee;
    };
    if head_len == 0 || !callee.is_char_boundary(head_len) {
        return callee;
    }
    let (head, tag) = callee.split_at(head_len);
    let Some(rest) = tag.strip_prefix(TRUST_ARGS_FINGERPRINT_PREFIX) else { return callee };
    let Some(hex) = rest.strip_suffix('>') else { return callee };
    // LOWERCASE only: `{:016x}` never emits `A`..`F`.
    if hex.len() == TRUST_ARGS_FINGERPRINT_HEX_LEN
        && hex.bytes().all(|b| matches!(b, b'0'..=b'9' | b'a'..=b'f'))
    {
        head
    } else {
        callee
    }
}

/// Does `callee` carry a duplicate-crate-name argument fingerprint ANYWHERE?
/// When it does, some def named in its generic arguments lives in a crate whose
/// rendered name does not identify it, so a TYPE PATH read out of those
/// arguments (`core::ops::range::RangeFull`) may be a same-named crate's type:
/// such a reader must decline. Anywhere, not only trailing: other verifier
/// markers can be stacked after it, and `@` is not an identifier character, so
/// source cannot spell the opener.
#[must_use]
pub fn args_display_may_name_a_same_named_crate(callee: &str) -> bool {
    callee.contains(TRUST_ARGS_FINGERPRINT_PREFIX)
}

#[cfg(test)]
mod tests {
    use super::*;

    const DRAIN: &str =
        "alloc::collections::vec_deque::VecDeque::<u32>::drain::<core::ops::range::RangeFull>";

    /// The producer's own test vector (`convert.rs`
    /// `disambiguate_generic_call_path(path, Some(Fingerprint::new(0x1, 0x23)))`)
    /// renders exactly this; the renderer here must agree byte for byte.
    #[test]
    fn renderer_matches_the_producer_spelling() {
        assert_eq!(
            render_trailing_args_fingerprint(0x1, 0x23),
            "::<__trust_args@00000000000000010000000000000023>"
        );
    }

    #[test]
    fn strips_exactly_one_canonical_trailing_tag() {
        // Measured spelling: the `drain(..)` callee of `repro-clean/drain_dupname.rs`
        // as preview3 stage1 rendered it in the two-`dupdep` graph.
        let measured = "alloc::collections::vec_deque::VecDeque::<u32>::drain\
                        ::<core::ops::range::RangeFull>\
                        ::<__trust_args@bc8470b1bce69c383692fbc2a19ba857>";
        assert_eq!(strip_trailing_args_fingerprint(measured), DRAIN);
        let tagged = format!("{DRAIN}{}", render_trailing_args_fingerprint(0x9e8e, 0xac84));
        assert_eq!(strip_trailing_args_fingerprint(&tagged), DRAIN);
        // One tag only: a doubled tag (never produced) keeps its inner one.
        let doubled = format!("{tagged}{}", render_trailing_args_fingerprint(1, 2));
        assert_eq!(strip_trailing_args_fingerprint(&doubled), tagged);
    }

    #[test]
    fn untagged_paths_are_unchanged() {
        assert_eq!(strip_trailing_args_fingerprint(DRAIN), DRAIN);
        assert_eq!(strip_trailing_args_fingerprint("crate::f"), "crate::f");
        assert_eq!(strip_trailing_args_fingerprint(""), "");
    }

    /// NEGATIVE: every lookalike the grammar must refuse keeps the whole path.
    #[test]
    fn lookalikes_are_not_stripped() {
        for s in [
            // A user type genuinely named `__trust_args` (writable Rust).
            "mycrate::f::<__trust_args>",
            "mycrate::f::<mycrate::__trust_args>",
            // Wrong hex length (31, 33), uppercase, non-hex.
            "f::<__trust_args@8a2184a43a70782505085d99a82ff88>",
            "f::<__trust_args@8a2184a43a70782505085d99a82ff8866>",
            "f::<__trust_args@8A2184A43A70782505085D99A82FF886>",
            "f::<__trust_args@8a2184a43a70782505085d99a82ff88g>",
            // Missing `@`, missing `::`, missing `>`.
            "f::<__trust_args8a2184a43a70782505085d99a82ff8861>",
            "f<__trust_args@8a2184a43a70782505085d99a82ff886>",
            "f::<__trust_args@8a2184a43a70782505085d99a82ff886",
            // Not trailing.
            "f::<__trust_args@8a2184a43a70782505085d99a82ff886>::g",
            // No head.
            "::<__trust_args@8a2184a43a70782505085d99a82ff886>",
        ] {
            assert_eq!(strip_trailing_args_fingerprint(s), s, "{s}");
        }
    }

    #[test]
    fn tag_anywhere_marks_the_argument_display_as_crate_ambiguous() {
        let tagged = format!("{DRAIN}{}", render_trailing_args_fingerprint(1, 2));
        assert!(args_display_may_name_a_same_named_crate(&tagged));
        assert!(args_display_may_name_a_same_named_crate(&format!(
            "{tagged}::<__trust_str_index>"
        )));
        assert!(!args_display_may_name_a_same_named_crate(DRAIN));
        assert!(!args_display_may_name_a_same_named_crate("mycrate::f::<__trust_args>"));
    }

    /// The other trailing verifier markers are a different grammar and are not
    /// this helper's to remove.
    #[test]
    fn other_trust_markers_are_not_stripped() {
        for s in [
            "core::ops::index::Index::index::<__trust_args@00112233445566778899aabbccddeeff>\
             ::<__trust_str_index>",
            "alloc::vec::from_elem::<u8>::<__trust_elem_bytes@1>",
            "crate::f::<__trust_alias@00112233445566778899aabbccddeeff>",
        ] {
            assert_eq!(strip_trailing_args_fingerprint(s), s, "{s}");
        }
    }
}
