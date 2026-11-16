//! Run WP's native body cases in the router's actual dependency family.
//! Reuse the component's original questions and adversarial controls.

#![cfg(feature = "trust-build")]

#[path = "../../../first-party/trust-wp/crates/trust-wp-lib/tests/trust_ir_native_bundle.rs"]
mod native_bundle;

#[path = "../../../first-party/trust-wp/crates/trust-wp-core/tests/mixed_boolean_integer.rs"]
mod mixed_boolean_integer;
