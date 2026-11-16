//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Coverflow-checks=on -Zinline-mir=no -Zalways-encode-mir
//@ edition: 2021
//@ no-prefer-dynamic
//! A dependency compiled the way `targo` compiles every dependency unit
//! (`-Ztrust-verify=off`, plus `-Zalways-encode-mir` so a caller that declares
//! this crate in its bundling scope can bundle these bodies), with overflow
//! checks ON. Its own codegen keeps every overflow check, so each function
//! below panics with `attempt to add with overflow` at `u32::MAX`, whatever the
//! caller's overflow-checks setting (OVF-ASSERT-XCRATE-1).
//!
//! `-Zinline-mir=no` keeps `outer`'s call to `inner` a call, so the caller's
//! bundle holds `inner` as its own member.

/// The measured witness (scout20 `confirm1/dep2.rs`): exported, so the
/// dependency's code runs on every call.
#[inline(never)]
pub fn inc(x: u32) -> u32 {
    x + 1
}

/// Cross-crate-inlinable: the crate whose code calls it codegens its own copy.
#[inline]
pub fn inner(x: u32) -> u32 {
    x + 1
}

/// Exported, so the copy of `inner` it runs is THIS crate's, with checks on.
#[inline(never)]
pub fn outer(x: u32) -> u32 {
    inner(x)
}
