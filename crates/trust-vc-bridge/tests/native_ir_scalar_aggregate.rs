//! Run the published VC scalar controls against Root's actual dependency family.
//!
//! The workspace bridge selects its committed IR, engine and certificate features.
//! Reuse the component's cases and fixtures so this boundary adds no second
//! description of scalar semantics, source assumptions or proof authority.

#![cfg(feature = "trust-build")]

#[path = "../../../first-party/trust-vc/crates/trust-vc-trust-engine/tests/trust_ir_body_aggregate.rs"]
mod aggregate;

#[path = "../../../first-party/trust-vc/crates/trust-vc-trust-engine/tests/trust_ir_body_boolean.rs"]
mod boolean;

#[path = "../../../first-party/trust-vc/crates/trust-vc-trust-engine/tests/trust_ir_body_certificate.rs"]
mod certificate;
