//! On-disk witness schema identifiers.
//!
//! The witness is a per-root, structurally-canonical encoding of the full
//! downstream-consumed `TypeckResults` surface. Version is bumped on any
//! grammar change so a stale-schema witness is a clean miss, never a
//! misdecode.

/// Schema version string, folded into the witness key so a schema change
/// invalidates every stored witness.
// v2: adds the method/operator-pick record (type_dependent_defs +
// used_trait_imports) for the monomorphic-pick enabled-set widening. Folded into
// the witness key, so stale v1 stores miss cleanly.
// v3 (soundness audit 2026-07-22): the enabled set was narrowed to close four
// confirmed checker-blind holes — non-Rust-ABI / splatted fn-pointer TYPES are
// no longer minted (ABI/splatted are not round-tripped; decode rebuilt Rust),
// offset_of! roots are excluded (offset_of_data is not encoded), and picks in
// typeck-CHILD bodies (inline/anon consts the root-body checker never walks) are
// rejected. Bumping the version guarantees no pre-fix v2 witness — which could
// carry any of that unvalidated data — is ever loaded by the fixed compiler.
// v4 (soundness audit follow-up): v3 rejected only method picks in unchecked
// child bodies, while every other child-owned TypeckResults map remained
// installable. Replay now admits only a root whose primary body is its sole
// HIR body, decode validates every serialized ItemLocalId before insertion,
// and mint requires every unencoded TypeckResults field to be empty.
// v5 (scope widening 2026-07-23): the fn-pointer tag-14 encoding now round-trips
// the ABI (an `as_packed` byte after the safety byte, decoded via
// `ExternAbi::from_packed`), re-admitting non-Rust-ABI fn-ptr TYPES that v3
// conservatively escaped. The byte format changed, so v4 stores must miss cleanly.
pub const SCHEMA_VERSION: &str = "trust.typeck-witness.v6";

/// Magic prefix on every per-root witness payload (replay-capable form:
/// full 128-bit `DefPathHash`es, distinct from the size-only P0WF probe).
pub const WITNESS_MAGIC: &[u8; 4] = b"TWV1";

/// Magic prefix on a packed crate store (`<StableCrateId>.twit`).
// TWSTORE2: per-entry integrity digest added (store.rs `entry_digest`). Old
// TWSTORE1 stores fail the magic check => clean whole-store MISS (fail-safe).
pub const STORE_MAGIC: &[u8; 8] = b"TWSTORE2";
