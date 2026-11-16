//@ no-prefer-dynamic
//@ compile-flags: -Z trust-verify=off
#![crate_type = "rlib"]

//! **A PURE SPEC crate: a `clean { … }` island that mints nothing.**
//!
//! This is the flagship shape for a workspace's one spec crate, and until
//! cross-crate proof citation increment 2 it transported NOTHING. The rmeta
//! encoder consulted the MINT REGISTRY (`clean_origin_defs`) before writing a
//! single island byte, a `theorem` is filtered out of the mint by
//! construction, and a crate whose islands are proof-only therefore wrote two
//! empty arrays — so a dependent could not have cited these theorems even
//! after the composition that re-elaborates them was written.
//!
//! The encoder now writes the island sources, plus a
//! `trust_clean_proof_manifest` (kernel version + source digest), whenever the
//! crate HAS islands. Nothing about THIS crate's own verdicts changes: no
//! `def`, no mint, no `VerdictDigest`, no CALL capability — the island below
//! is a theorem and nothing else.
//!
//! `clean_citation_cross_crate_options.rs` is the consumer, and it is the
//! end-to-end witness that the bytes crossed: the notes it pins can only be
//! produced from a manifest this crate transported.

clean {
    theorem cap_le_bound : 0 = 0 := rfl
}
