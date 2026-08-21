//! **I7 transport control — the exporting side.**
//!
//! Same shape as `tests/ui/trust/auxiliary/clean_origin_aux.rs`: `pick` is
//! minted from the island (Projection fragment, parameter 0), gated by the
//! sole constructor, and — because this crate is built as an rlib dependency —
//! exported through the I7 encode half: a `trust_clean_verdict_digest` row,
//! the island sources, and the `trust_clean_origin_exports` list all land in
//! this crate's rmeta. The digest row is the byte-patch target: its wire
//! format (`crates/trust-clean-origin/src/admission.rs`, `VerdictDigest`)
//! begins with the four-byte digest magic, then `format u8 · decl ·
//! kernel_version`, each string u32-LE length-framed, and `rmake.rs` rewrites
//! the `kernel_version` VALUE in place.
//!
//! Do NOT spell the magic bytes in this file: doc comments are encoded into
//! the rmeta, and a literal copy of the magic here is a second match for the
//! locator scan `rmake.rs` asserts is unique (measured 2026-08-20: the first
//! draft of this very comment produced exactly that duplicate).
//!
//! The module is `pub` deliberately (I7 review, defect 2): the mint forces the
//! DEF's visibility to `Public`, but nothing touches the module's.

pub mod m {
    clean {
        def pick (x y : UInt64) : UInt64 := x
    }
}
