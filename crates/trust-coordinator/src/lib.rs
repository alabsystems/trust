// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Shared memory admission for Trust clients and the `trustd` daemon.
//!
//! The protocol, process ownership, refusal rules and both admission transports
//! have one implementation. This crate has no solver or verifier dependency on
//! Unix, so building the daemon does not rebuild the verification backends.

pub mod coordinator;
pub mod memory_jobserver;
