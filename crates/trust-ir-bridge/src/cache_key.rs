//! Verification-cache content key derived from the trust-ir spine module.
//!
//! [`module_stable_content_hash`] turns a FAITHFULLY-lowered spine module into a
//! canonical, MIR-renumber-immune content-hash string: the RATIFIED
//! `Module::stable_digest()` over the module's stable binary serialization
//! (order-stable, id-renumber-immune — see trust-ir `TRUST.md` build-determinism
//! guarantee), rendered as the digest's stable `Display` form
//! `<algorithm>:<hex>` (the algorithm tag is owned by trust-ir and versions
//! with the digest domain, so a digest-scheme bump can never alias an old key).
//!
//! # Where this fits in the caching stack
//!
//! The persistent solver cache (`trust_router::solver_cache`) already keys
//! per-VC on a canonicalized formula hash, so re-SOLVING is skipped on warm
//! runs. What it cannot skip is the per-function work UPSTREAM of the formulas
//! — extraction, spine lowering, and VC generation — because the in-compiler
//! artifact cache (`SessionArtifactCache`) is invocation-scoped. A persistent
//! per-function artifact experiment benefits from a stable observation key
//! that does not spuriously miss when unrelated edits renumber MIR
//! locals/blocks. The ratified module digest supplies that observation identity;
//! it is not, by itself or with the current compiler facets hash, proof authority
//! for reusing a generated obligation vector.
//!
//! # Soundness precondition (REQUIRED — this is a false-PROVE surface)
//!
//! The caller MUST pass a module produced by [`crate::lower_to_trust_ir`]
//! returning `Ok` for the function whose artifacts are being keyed, i.e. a
//! `Some(spine_module)` on the verify path. That lowering is FAIL-CLOSED for
//! TYPES AND OPS: `map_type` / `map_binop` / `map_unop` / aggregate-kind
//! validation each return `Err(BridgeError::Unsupported*)` on anything they
//! cannot represent, so an `Ok` module contains every type and op of the
//! function.
//!
//! **The digest does NOT cover every verification-relevant input.** The
//! contract loop deliberately NO-OPS `ContractKind::Decreases` and
//! `ContractKind::Modifies` (they produce no ProofObligation and contribute
//! zero bytes to the serialized module), yet both drive live solver VCs in
//! trust-vcgen (loop-decreases / frame-condition obligations). A future
//! proof-authoritative caller would have to bind the complete original
//! `VerifiableFunction`, every contract and callee/spec input, every
//! `VcgenContext` field, explicit generator inputs such as synthesized Box-deref
//! spans, and a collision-resistant canonical generator/schema identity. The
//! compiler's current `vc_artifact_facets_hash` is telemetry-only and does not
//! establish that envelope.
//!
//! If a function does NOT lower (`Err` / `None`), an observation keyed here must
//! miss. Even for an `Ok` lowering, a hit may only drive metrics/population;
//! fresh generation remains mandatory. Re-solving a cached, truncated vector
//! cannot recover an omitted obligation and could otherwise false-PROVE.
//!
//! Any callee-contract fingerprint (spec drift) must remain a SEPARATE key
//! component alongside this content hash — the module digest covers the
//! function's own lowered content, not its callees' contracts.

use trust_ir::Module;

/// Canonical content-hash string for a faithfully-lowered spine module.
///
/// See the module docs: this is a stable content identity for a lowered module,
/// not a completeness certificate for VC-generation inputs or outputs.
#[must_use]
pub fn module_stable_content_hash(module: &Module) -> String {
    module.stable_digest().to_string()
}

#[cfg(test)]
mod tests {
    use trust_ir::Module;

    use super::module_stable_content_hash;

    #[test]
    fn hash_is_canonical_algorithm_prefixed_hex() {
        // Canonical `<algorithm>:<64 hex>` shape, without pinning the algorithm
        // tag: trust-ir owns it and versions it with the digest domain (v1 was
        // `trust_ir-stable-v1:`, v2 is `sha256:` over the `trust_ir.module.v2`
        // domain) — a scheme bump changes the prefix and so can never alias a
        // key from the old scheme.
        let h = module_stable_content_hash(&Module::new("f"));
        let (alg, hex) = h.split_once(':').expect("digest must be `<algorithm>:<hex>`");
        assert!(!alg.is_empty(), "algorithm tag must be non-empty, got {h:?}");
        assert_eq!(hex.len(), 64, "digest must be 32 bytes of hex, got {h:?}");
        assert!(
            hex.bytes().all(|b| b.is_ascii_hexdigit()),
            "digest payload must be hex, got {h:?}"
        );
    }

    #[test]
    fn hash_is_deterministic_for_equal_modules() {
        // Same module content lowered/built twice hashes identically — the
        // property a warm cache relies on (no spurious miss on a rebuild).
        let a = module_stable_content_hash(&Module::new("same"));
        let b = module_stable_content_hash(&Module::new("same"));
        assert_eq!(a, b, "equal modules must produce equal content hashes");
    }

    #[test]
    fn hash_discriminates_on_module_content() {
        // A content difference (here: the module/function name) must perturb the
        // hash, or a cache would serve one function's verdict for another —
        // the soundness direction (no false hit on changed content).
        let a = module_stable_content_hash(&Module::new("alpha"));
        let b = module_stable_content_hash(&Module::new("beta"));
        assert_ne!(a, b, "distinct module content must produce distinct hashes");
    }
}
