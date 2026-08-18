//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ no-prefer-dynamic
//! An ORDINARY dependency — ordinary crate name, no `--crate-name` trick, no
//! impersonation of anything — whose only unusual property is that one of its
//! inherent functions is called `map`.
//!
//! `Endless::next` NEVER returns `None`. `Adapt::map` and `Adapt::nudge` have
//! byte-identical bodies and signatures; they differ only in their name.
//!
//! Rendered from a consumer, the two calls are
//!
//! ```text
//! mycrate::Adapt::map
//! mycrate::Adapt::nudge
//! ```
//!
//! `trust_vcgen::generate::alloc_vcs::is_len_preserving_adaptor` tested the LAST
//! PATH SEGMENT of the callee and nothing else, so `map` stepped the
//! bounded-source walk through to argument 0 — where it found a genuine
//! `core::slice::<impl [u8]>::iter` and concluded the collect was bounded, while
//! `nudge` did not. One identifier, and the consumer's whole
//! unbounded-allocation obligation disappears.
#![allow(dead_code)]
#![crate_name = "mycrate"]

/// An iterator whose `next` never returns `None`: collecting it allocates
/// without bound in every execution.
pub struct Endless {
    pub i: u64,
}

impl Iterator for Endless {
    type Item = u8;
    #[inline(never)]
    fn next(&mut self) -> Option<u8> {
        self.i = self.i.wrapping_add(1);
        Some(0)
    }
}

pub struct Adapt;

impl Adapt {
    /// NOT `core::iter::Iterator::map` — an inherent function on a user type
    /// whose last path segment happens to be `map`.
    #[inline(never)]
    pub fn map(_src: core::slice::Iter<'_, u8>, _f: u8) -> Endless {
        Endless { i: 0 }
    }

    /// Byte-identical to [`Adapt::map`] but for the name.
    #[inline(never)]
    pub fn nudge(_src: core::slice::Iter<'_, u8>, _f: u8) -> Endless {
        Endless { i: 0 }
    }
}
