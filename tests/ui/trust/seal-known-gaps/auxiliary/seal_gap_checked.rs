//@ edition: 2021
//@ compile-flags: --crate-type=rlib --emit=metadata -Ztrust-verify=off -A warnings
//@ no-prefer-dynamic
//! A dependency of `cb_n1_f1_unread_body_carries_cut_note.rs` and
//! `cb_n2_closure_in_assoc_const_named_as_const.rs` (the review of the
//! check-build fix `332dfad2ee`, 2026-10-16), built as `cargo check` builds
//! one: metadata only, so its metadata carries no MIR for its generic fn, nor
//! for the closure its blanket impl puts in a constant (the constant's own
//! MIR, for evaluation, it does carry). Safe and sound: nothing here writes
//! what it is handed.
//! Copyright 2026 Andrew Yates | License: Apache 2.0
#![forbid(unsafe_code)]

/// Reads the size of what it is handed.
pub fn measure<T>(t: &T) -> usize {
    std::mem::size_of_val(t)
}

/// A constant fn pointer for every type: a closure that reads a size.
pub trait HasC {
    const C: fn(&Self) -> usize;
}

impl<T> HasC for T {
    const C: fn(&T) -> usize = |t| std::mem::size_of_val(t);
}
