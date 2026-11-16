// Trust: cross-crate PROOF-position citation, increment 2 (TRANSPORT).
//
//! The manifest that travels beside a crate's `clean { … }` island sources so
//! a dependent crate can say *which* proof material it re-elaborated.
//!
//! # Why this is not the certificate lane
//!
//! Cross-crate CALL (I7) transports a `VerdictDigest` per Clean-origin def and
//! readmits it at the extern MIR decode chokepoint. Cross-crate PROOF
//! transports nothing of the kind: a `theorem` is never minted, carries no
//! digest, and grants no capability. What crosses here is **text**, and the
//! consuming compiler re-elaborates and kernel-checks every byte of it under
//! its OWN kernel before a single contract may cite it.
//!
//! So the two fields below are not authority and are never compared in place
//! of a check:
//!
//! * `kernel_version` is the Clean kernel the producing compiler linked. The
//!   consumer compares it against its own and refuses *before* any
//!   elaboration when they differ — not because a matching version would make
//!   the sources acceptable, but because re-checking a proof under a silently
//!   different kernel is exactly the substitution that must not be silent.
//! * `source_digest` identifies WHICH bytes were published. The consumer
//!   recomputes it over the bytes that actually arrived and refuses on a
//!   disagreement, so a stale or partially written `.rmeta` is reported as one
//!   instead of surfacing as a contract proved from a declaration the
//!   dependency does not have.
//!
//! Both checks live in `trust_certify::clean_island::extern_proof`, which owns
//! the one definition of the digest (`extern_proof_source_digest`) used by the
//! producing and the consuming side alike.
//!
//! The crate's identity (`name`, `StableCrateId`) is NOT repeated here: the
//! `CrateRoot` already carries both, and a second copy is a second thing that
//! can disagree.

use rustc_macros::{Decodable, Encodable, StableHash};

/// Trust: one crate's Clean PROOF transport manifest. Present for every crate
/// that has at least one `clean { … }` island, whether or not that island
/// minted anything callable — a pure spec crate is the flagship shape and it
/// mints nothing at all.
#[derive(StableHash)]
#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord, Encodable, Decodable)]
pub struct TrustCleanProofManifest {
    /// `clean_kernel::VERSION` as linked by the compiler that produced the
    /// transported island sources.
    pub kernel_version: String,
    /// `trust_certify::clean_island::extern_proof_source_digest` over
    /// `(crate name, stable crate id, kernel_version, island sources)`, taken
    /// over the exact bytes this crate transported, in authored order.
    pub source_digest: String,
}
