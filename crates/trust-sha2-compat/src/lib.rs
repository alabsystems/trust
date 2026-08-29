// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![cfg_attr(not(feature = "std"), no_std)]

//! **The package name `sha2`, bound to Trust-owned SHA-2.**
//!
//! This crate contains no cryptography. Every item below is a re-export of
//! [`trust_sha2`], which is the FIPS PUB 180-4 implementation and carries all
//! of the evidence — spec-derived constant tables, NIST CAVP known-answer
//! vectors, padding-boundary and chunk-independence tests, and the
//! differential against the incumbent. Read `crates/trust-sha2/src/lib.rs`
//! for that; do not restate it here, because a second copy of an evidence
//! claim is a copy that can go stale while the first one moves.
//!
//! # What this crate is for
//!
//! `[patch.crates-io]` substitutes a package by NAME and VERSION, and cannot
//! rename. That is why `crates/trust-sha2` — whose package name is
//! `trust-sha2` — cannot itself be the patch target, and why the alias in
//! `crates/Cargo.toml`
//!
//! ```text
//! sha2 = { package = "trust-sha2", path = "trust-sha2" }
//! ```
//!
//! reaches only the manifests this repository owns. The `first-party/*`
//! submodules declare `sha2 = "0.10"` in manifests we cannot edit without
//! breaking their standalone builds, so they are reached the other way: a
//! patch at the workspace root being built, which cargo applies graph-wide.
//! This crate exists to be the thing that patch points at. See
//! `crates/trust-memchr` for the executed precedent of the same shape.
//!
//! # The risk this crate carries, and the test that covers it
//!
//! An alias is not neutral. Thirty-two crates across seven repositories
//! compute cache keys, certificate identities and provenance records through
//! the name `sha2`, and they will keep compiling if this crate re-exports
//! something that merely has the right shape. The failure would be silent and
//! it would be an identity change: artifacts that should share a digest stop
//! sharing it.
//!
//! `tests/compat_surface.rs` therefore does two things that the trust-sha2
//! test suite cannot do from inside trust-sha2:
//!
//! 1. It pins published FIPS 180-4 / NIST digests **through this crate's own
//!    name**, so the re-export is proven to reach the real implementation and
//!    not a look-alike.
//! 2. It exercises the four call shapes measured across the sibling
//!    repositories, in their measured proportions, so a re-export that is
//!    merely *incomplete* fails to compile here rather than at a consumer.
//!
//! # Surface, and what is deliberately missing
//!
//! Provided: [`Digest`], [`Sha224`], [`Sha256`], [`Sha384`], [`Sha512`] and
//! the four output types.
//!
//! Not provided, because nothing in this tree uses them: `Sha512_224`,
//! `Sha512_256`, the `*VarCore`/`*Core` block-level types, the re-exported
//! `digest` module, and the RustCrypto trait vocabulary (`HashMarker`,
//! `FixedOutput`, `OutputSizeUser`, `Update`, `Reset`, `AssociatedOid`,
//! `GenericArray`).
//!
//! A missing *item* fails loudly and locally — `unresolved import
//! sha2::Sha256`, at the consumer. Note the asymmetry with a missing
//! *feature*, which does not fail at all: it silently drops that consumer back
//! to the incumbent crate. See the `[features]` comment in `Cargo.toml`; that
//! difference was measured, not assumed, and it is the one trap in this
//! crate.
//!
//! That last omission is load-bearing and it is the one thing to know before
//! widening a `[patch.crates-io]` to a new workspace: `ed25519-dalek` and
//! `curve25519-dalek` are generic over RustCrypto's `digest::Digest` and
//! require `Sha512: HashMarker`. They do not compile against this crate. The
//! failure is loud (`the trait bound Sha512: digest::Digest is not
//! satisfied`), not silent, so it gates rather than corrupts — but it means a
//! graph containing dalek must replace it, or gain a `digest`-trait shim,
//! before it can be patched.

pub use trust_sha2::{
    Digest, Digest28, Digest32, Digest48, Digest64, Sha224, Sha256, Sha384, Sha512,
};
