// T5A regression, safe-std::ffi face: 100%-safe code whose call paths live
// under the `std::ffi` / `std::env` NAMESPACES (`OsStr::to_str`,
// `OsString::push`, `env::vars_os().collect()`) must verify with ZERO
// missing-SAFETY demands. Pre-T5A the "::ffi::" UNSAFE_PATTERNS entry matched
// the namespace substring and demanded SAFETY comments on every such call
// (the aterm-uds 4 / aterm-types 2 / aterm-pty up-to-29 false-demand class).
// Unsafe-call detection now keys on the AUTHORITATIVE
// `Terminator::Call::is_unsafe_sig` (tcx.fn_sig safety, recorded at
// extraction) — false for every call below — so no unsafe block exists here.
// This file must PROVE (exit 0) with no SAFETY demands.
#![crate_type = "lib"]

use std::ffi::{OsStr, OsString};

/// `OsStr::to_str` is a SAFE fn under the std::ffi namespace — the canonical
/// false-demand shape (aterm-uds config-path handling).
#[must_use]
pub fn utf8_name(name: &OsStr) -> Option<&str> {
    name.to_str()
}

/// `OsString::push` — safe mutation under std::ffi (aterm-types PATH glue).
#[must_use]
pub fn join_extension(mut base: OsString, ext: &OsStr) -> OsString {
    base.push(".");
    base.push(ext);
    base
}

/// `env::vars_os()` iterates `(OsString, OsString)` pairs — safe end to end,
/// but every adapter in the chain resolves under std::ffi paths (aterm-pty
/// environment forwarding).
#[must_use]
pub fn snapshot_env() -> Vec<(OsString, OsString)> {
    std::env::vars_os().collect::<Vec<(OsString, OsString)>>()
}
