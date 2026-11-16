//@ needs-trust-verify
//@ edition: 2021
//@ revisions: zero_sized_receiver byte_receiver range_from_zipped_source
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//@[zero_sized_receiver] check-fail
//@[byte_receiver] check-pass
//@[range_from_zipped_source] check-fail
//! **`extend` into a `Vec` of a zero-sized element keeps its capacity obligation
//! (Trust, 2026-09-29).**
//!
//! `extend` reserves from its source's `size_hint`, and the allocation lane skips the
//! capacity-overflow obligation when the source is an existing bounded collection:
//! memory bounds what can be added. That argument needs the RECEIVER's length bounded
//! by memory too. A `Vec<()>` can already hold `usize::MAX` elements, and
//! `v.extend(Some(()))` then panics "capacity overflow"; it was proved panic-free in
//! both lanes (the zero-size rule's precondition audit, `p10`). The skip now also
//! requires the receiver's element to be at least one byte
//! (`alloc_vcs::extend_receiver_element_is_nonzero_sized`).
//!
//! * `zero_sized_receiver`: NEGATIVE — the obligation is kept and not discharged.
//! * `byte_receiver`: POSITIVE — a `Vec<u8>` holds at most `isize::MAX` bytes.
//! * `range_from_zipped_source`: NEGATIVE. The extractor's total-call rewrite erases
//!   the whole `extend`, and with it every `next` of the source. `Zip` was licensed when
//!   EITHER side was a bounded collection, so `(250u8..).zip(s)` was erased, while
//!   `RangeFrom::next` panics "attempt to add with overflow" on its seventh item (the
//!   round-2 precondition audit, `q15`). Both sides must now be bounded collections.

#[cfg(zero_sized_receiver)]
pub fn add_one_unit(v: &mut Vec<()>) {
    //[zero_sized_receiver]~^ ERROR Trust
    v.extend(Some(()));
}

#[cfg(byte_receiver)]
pub fn add_one_byte(v: &mut Vec<u8>) {
    v.extend(Some(7u8));
}

#[cfg(range_from_zipped_source)]
pub fn tag_bytes(v: &mut Vec<(u8, u8)>, s: &[u8]) {
    //[range_from_zipped_source]~^ ERROR Trust
    v.extend((250u8..).zip(s.iter().copied()));
}
