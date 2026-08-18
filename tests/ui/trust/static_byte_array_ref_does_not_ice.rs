//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
//! Taking `&SOME_STATIC` where the static is a `[u8; N]` must not abort the
//! compiler. `array_ref_u8_const_bytes` reads the pointed-to allocation to
//! recover a `core::fmt::Arguments` byte template, and it used to call
//! `GlobalAlloc::unwrap_memory()`. A `&'static [u8; N]` that points at a
//! `static` has `GlobalAlloc::Static`, not `Memory`, so `unwrap_memory` hit
//! rustc's own `bug!("expected memory, got {:?}")` and killed the crate:
//!
//! ```text
//! error: internal compiler error: crates/trust-mir-extract/src/convert.rs:2749:51:
//!        expected memory, got Static(DefId(0:3 ~ w3[f019]::OFFSETS))
//! ```
//!
//! Three lines of ordinary safe code reproduce it, so this was not a std-only
//! shape. It is also why `core` could not be compiled with verification on at
//! all: `core::unicode::unicode_data::alphabetic::OFFSETS` is exactly this.
//!
//! A `const` item does NOT reproduce it — those promote to an anonymous
//! `Memory` allocation — which is why the byte-template reader survived this
//! long. Only a named `static` reaches the `Static` arm.
//!
//! The fix degrades to `None` (the const stays an opaque `OpaqueConst`) like
//! every other exit in this exact-or-`None` reader, so it loses precision and
//! can never mint a proof.
#![crate_type = "lib"]
#![no_std]

static OFFSETS: [u8; 4] = [1, 2, 3, 4];

// The bare reference is the whole trigger; no indexing needed.
pub fn probe_static_byte_array_ref() -> &'static [u8; 4] {
    &OFFSETS
}

// The indexed form ICEd identically. Its bound comes from the ARRAY TYPE
// (`[u8; 4]`), not from the allocation contents, so opaquing the const does not
// cost the bounds proof.
pub fn probe_static_byte_array_index(i: usize) -> u8 {
    let table: &[u8; 4] = &OFFSETS;
    table[i % 4]
}

// A `const` item took the `Memory` arm and always worked. Pinned so a future
// rewrite of the reader cannot regress the case that did work.
const CONST_OFFSETS: [u8; 4] = [5, 6, 7, 8];

pub fn probe_const_byte_array_ref() -> &'static [u8; 4] {
    &CONST_OFFSETS
}
