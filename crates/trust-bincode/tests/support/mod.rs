// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Shared support for the integration tests. Not a test target itself.

#![allow(dead_code)]

pub mod big_enum;
// DEAD as of the serde_json switch — DELETE THIS LINE AND `json.rs` when the
// crate is first committed.
//
// `json.rs` is a hand-rolled strict JSON reader written when this crate had no
// JSON dev-dependency. `tests/golden_bincode1.rs` now reads the fixture with
// `serde_json` (a dev-dependency; see `Cargo.toml` for why that is safe here
// and why the incumbent `bincode` is a different question). Nothing in this
// directory references `support::json` any more — verified by grep across both
// `mod support` consumers.
//
// It is left in place rather than deleted only because this crate is still
// UNTRACKED: `rm` would destroy it with no git history to recover it, while a
// concurrent lane is working in this same directory. Once `trust-bincode` is
// committed, deleting it is a two-line change with no reader to break.
pub mod json;
pub mod types;

/// Decode a lowercase hex string into bytes. Panics on malformed input,
/// because the only source is the committed fixture.
pub fn unhex(s: &str) -> Vec<u8> {
    assert!(s.len() % 2 == 0, "odd-length hex string {s:?}");
    (0..s.len() / 2)
        .map(|i| {
            u8::from_str_radix(&s[i * 2..i * 2 + 2], 16)
                .unwrap_or_else(|e| panic!("bad hex {s:?}: {e}"))
        })
        .collect()
}

/// Encode bytes as lowercase hex.
pub fn hex(bytes: &[u8]) -> String {
    use std::fmt::Write as _;
    let mut out = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        let _ = write!(out, "{b:02x}");
    }
    out
}
