//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=off
//@ proc-macro: trust.rs
//@ edition: 2021
//@ check-pass
//! Trust E9 — THE VANILLA HALF of the payoff shape: with verification off, a
//! cited contract attribute is not a contract at all.
//!
//! `cfg_attr` is why the attribute surface matters. `fn f(..) ensures P by T`
//! is a grammar stock rustc cannot parse, so a crate that uses it must
//! quarantine that code in a trustc-only file — which is exactly why every
//! citation in the veripb client sits on a hand-maintained twin instead of on
//! the code the program runs. `#[cfg_attr(trust_verify, trust::ensures(P by
//! T))]` is an ordinary attribute, and `trust_verify` is a COMPILER-PROVIDED
//! cfg (`rustc_session/src/config/cfg.rs`) set exactly when verification is
//! active. It is NOT settable with `--cfg` (trustc rejects that as an explicit
//! builtin cfg), and stock rustc never defines it — so the gate is automatic
//! in both directions.
//!
//! `-Ztrust-verify=off` is this file's whole point: it is the vanilla mode the
//! resolver's spec-contract hook is documented to leave bit-for-bit upstream.
//! Two independent things then make the payload inert — `cfg(trust_verify)` is
//! unset so `cfg_attr` strips the attribute, and even an unstripped
//! `trust::ensures` stays the stable-Rust passthrough proc macro.
//!
//! `would_not_parse_if_anything_read_it` is the sharp witness: its citation is
//! MALFORMED (`by Clean.` has a dangling dot) and is a hard error the moment
//! the contract parser sees it — see
//! `trust-spec-attribute-citation-dangling-dot.rs`. This file compiling means
//! nothing read it.
//!
//! The verifying half — the same spelling discharging against a Clean theorem
//! — is `trust-spec-attribute-citation.rs`. That stock rustc itself accepts
//! this source is not testable here (compiletest only runs trustc); it is
//! measured directly against a stock toolchain.

#![allow(unexpected_cfgs)]

#[cfg_attr(trust_verify, trust::ensures(result <= x by self_le))]
pub fn keep(x: u64) -> u64 {
    x
}

#[cfg_attr(trust_verify, trust::ensures(result <= x by Clean.))]
pub fn would_not_parse_if_anything_read_it(x: u64) -> u64 {
    x
}

fn main() {}
