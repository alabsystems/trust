//@ check-pass
//@ compile-flags: -Ztrust-verify=off -Ztrust-ir-lower=on --crate-type=lib
//! Trust (2026-09-22): **a `repr(transparent)` struct whose carrier the producer spells on a
//! narrowing lane must not DECLARE rustc's layout over that spelling.**
//!
//! `register_struct` fills `size`/`align`/offsets from `tcx.layout_of` and spells the field
//! types itself. Two of its lanes are coherent but unfaithful by design: `&mut dyn`/`&mut [T]`/
//! `&mut str` ride the thin `Ty::Ptr` arm (8 bytes for rustc's 16), and an `Option` whose
//! payload `enum_variant_field_admissible` declines (a fn pointer, a tuple, an array, a fat
//! `&[T]`) becomes the `Ty::Bool` flag (1 byte). Beside an ORDINARY struct's layout both pass
//! every consumer rule — a field smaller and no more aligned than rustc's sits inside rustc's
//! own placement — but a transparent struct's layout IS its carrier's, and trust-ir's layout
//! authority (`shape.rs`, `size != carrier_size || align != carrier_align`) refuses the pair:
//!
//!     StructLayoutInconsistent { struct_id: N, reason: "declared layout is incoherent
//!     (overlap / containment / alignment / packed / transparent rule)" }
//!
//! MEASURED 2026-09-22 on ay's everyday lane (`-Ztrust-verify=off -Ztrust-ir-lower=strict`):
//! ay-sat's lib TEST target (structs 282 and 777 of the crate module) and ay-tla-bridge
//! (struct 32). The interior of every `Cell`/`RefCell`/`Mutex`/`OnceCell` is such a struct
//! (`UnsafeCell<T>`), as are `Pin<Ptr>` and `ManuallyDrop<T>`, so an `&mut dyn FnMut` behind a
//! `RefCell` — ay-sat's `ProofControl` — is enough. Each shape below reproduced the refusal
//! in isolation before the fix; the producer now withholds the layout claim (absent-fill, the
//! wave-LC policy already applied to `Ty::Unit`) when a field's emitted spelling cannot carry
//! rustc's bytes, and the module validates. A `.stderr` is deliberately absent: the pin is
//! that this lane prints NOTHING for these shapes.
#![allow(dead_code)]

use std::cell::{Cell, RefCell, UnsafeCell};
use std::io::Write;
use std::mem::ManuallyDrop;

/// `UnsafeCell<&mut dyn FnMut() -> bool>` behind a `RefCell`: ay-sat's `ProofControl`.
pub struct Control<'a> {
    keep_going: RefCell<&'a mut dyn FnMut() -> bool>,
    state: Cell<u8>,
}

pub fn control<'a>(keep_going: &'a mut dyn FnMut() -> bool) -> Control<'a> {
    Control { keep_going: RefCell::new(keep_going), state: Cell::new(0) }
}

pub fn control_state(c: Control<'_>) -> u8 {
    c.state.get()
}

/// The thin lane itself under a user `repr(transparent)`, and behind `ManuallyDrop`/`Cell`.
#[repr(transparent)]
pub struct ThinWriter<'a>(pub &'a mut dyn Write);

pub fn thin_writer<'a>(w: &'a mut dyn Write) -> ThinWriter<'a> {
    ThinWriter(w)
}

pub fn thin_writer_size(w: ThinWriter<'_>) -> usize {
    std::mem::size_of_val(&w)
}

pub struct Slices<'a> {
    pub kept: ManuallyDrop<&'a mut [u32]>,
    pub text: Cell<&'a mut str>,
}

pub fn slices<'a>(kept: &'a mut [u32], text: &'a mut str) -> Slices<'a> {
    Slices { kept: ManuallyDrop::new(kept), text: Cell::new(text) }
}

pub fn slices_len(s: Slices<'_>) -> usize {
    s.kept.len()
}

/// The Option flag lane under `UnsafeCell`: a fn pointer, a tuple, an array, a fat `&[u8]`.
pub struct Flags<'a> {
    pub hook: Cell<Option<fn(u32) -> u32>>,
    pub pair: Cell<Option<(u32, u32)>>,
    pub quad: Cell<Option<[u32; 4]>>,
    pub bytes: UnsafeCell<Option<&'a [u8]>>,
}

pub fn flags(bytes: &[u8]) -> Flags<'_> {
    Flags {
        hook: Cell::new(None),
        pair: Cell::new(None),
        quad: Cell::new(None),
        bytes: UnsafeCell::new(Some(bytes)),
    }
}

pub fn flags_any(f: Flags<'_>) -> bool {
    f.hook.into_inner().is_some() || f.pair.into_inner().is_some() || f.quad.into_inner().is_some()
}
