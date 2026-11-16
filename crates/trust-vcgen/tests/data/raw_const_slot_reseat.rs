// Counter-programs for the slot-write channel rule (`generate::own_storage_write_borrow`)
// and the scans that ask it: a local's SLOT is aliased through `&raw const` (MIR
// `AddressOf(false, place)` with no `Deref` in `place`), the pointer is cast to
// `*mut`, and the slot is written. Tree Borrows accepts that write (Stacked
// Borrows rejects it), so a verifier that assumes only what both models validate
// must treat `&raw const` of an owned place as a slot-write channel. Every
// `reseat_raw_const_*` body panics natively at `i == 3` (`len is 2` / `len is 0`),
// each `scalar_*` and `*param*` add overflows `250 + 10`, and `guard_then_raw_const`
// and the index-parameter bodies index at `usize::MAX` (all measured at -O0 and
// -O3); the `*_raw_mut_*` bodies are the SAME programs through `&raw mut`, the
// channel the list always named, and are the controls.
//
// EVERY BINDING WRITTEN THROUGH SUCH A POINTER IS `mut` (`let mut s`, `mut x`).
// The Rust Reference lists mutating bytes owned by an IMMUTABLE binding as UB, so
// `let s = ..; *(&raw const s as *mut _) = t` is UB under any aliasing model; only
// with a `mut` binding is the write defined (under Tree Borrows). Binding
// mutability does not reach `trust_types` (the extracted bodies of the two
// spellings are the same apart from names and spans), so the rule does not, and
// cannot, tell them apart: it counts the channel for both, which is sound for both.
//
// Fixtures: tests/fixtures/raw_const_slot_reseat_<fn>_mir.json, dumped from this
// file by Trust `main` stage 1 a7ea88986d with
//   rustc --edition 2024 --crate-type lib -Ztrust-verify-profile=unix_hardened \
//         -Ztrust-policy=advisory -Ztrust-dump=mir:<dir> \
//         crates/trust-vcgen/tests/data/raw_const_slot_reseat.rs
// run from the repository root (so `span.file` is already repo-relative; nothing
// in the dumps was edited).
#![allow(unused_mut)]

// Straight-line, shared slice local (never a mutable-pointer local).
pub fn reseat_raw_const_shared(a: &[u8; 8], b: &[u8; 2], i: usize) -> u8 {
    let mut s: &[u8] = a;
    let p = &raw const s as *mut &[u8];
    unsafe {
        *p = b;
    }
    if i < 8 { s[i] } else { 0 }
}

// Straight-line, `&mut [u8]` local (a mutable-pointer local: its BASE name is
// havoced at an opaque store, which kills the pointee, never the slot's length).
pub fn reseat_raw_const_mut(a: &mut [u8; 8], b: &mut [u8; 2], i: usize) -> u8 {
    let mut s: &mut [u8] = a;
    let p = &raw const s as *mut &mut [u8];
    unsafe {
        *p = b;
    }
    if i < 8 { s[i] } else { 0 }
}

// The reseat in a LOOP BODY and the index after the loop: the stale tie must not
// survive the path-definition fixpoint's outflow kill. This is the shape B2's
// plain-relation outflow kill (aebf15b1ed) turned from refuted into a
// kernel-certified proof.
pub fn reseat_raw_const_mut_loop(a: &mut [u8; 8], i: usize, n: usize) -> u8 {
    let mut s: &mut [u8] = a;
    let p = &raw const s as *mut &mut [u8];
    let mut k = 0usize;
    while k < n {
        unsafe {
            *p = &mut [];
        }
        k += 1;
    }
    if i < 8 { s[i] } else { 0 }
}

// The same loop over a shared slice local.
pub fn reseat_raw_const_shared_loop(a: &[u8; 8], b: &[u8; 2], i: usize, n: usize) -> u8 {
    let mut s: &[u8] = a;
    let p = &raw const s as *mut &[u8];
    let mut k = 0usize;
    while k < n {
        unsafe {
            *p = b;
        }
        k += 1;
    }
    if i < 8 { s[i] } else { 0 }
}

// A CALL writes the slot through the `&raw const`-derived pointer.
#[inline(never)]
pub fn reseat_through(p: *mut &[u8], b: &'static [u8]) {
    unsafe {
        *p = b;
    }
}

static TWO: [u8; 2] = [1, 2];

pub fn reseat_call_raw_const_shared(a: &[u8; 8], i: usize) -> u8 {
    let mut s: &[u8] = a;
    reseat_through(&raw const s as *mut &[u8], &TWO);
    if i < 8 { s[i] } else { 0 }
}

// (A `&raw const w.s` FIELD reseat is not here: the compiler refuses that MIR
// shape before verification — `ASSUMPTION [addr-of-field] ... recorded as an
// unverified assumption (NOT proved; strict mode rejects it)` — so no body reaches
// vcgen. The `Field` arm of the rule is pinned by a unit test instead.)

// ---- not only lengths: any fact about a `&raw const`-exposed local -----------
//
// The list is not a slice-length device: it is how every havoc learns that a
// local's slot can be written behind its back. A scalar's own value fact
// (`y == 5`) survived the same writes.

pub fn scalar_raw_const(x: u8) -> u8 {
    let mut y: u8 = 5;
    let p = &raw const y as *mut u8;
    unsafe {
        *p = 250;
    }
    y + x.min(10)
}

#[inline(never)]
pub fn poke(p: *mut u8) {
    unsafe {
        *p = 250;
    }
}

pub fn scalar_call_raw_const(x: u8) -> u8 {
    let mut y: u8 = 5;
    poke(&raw const y as *mut u8);
    y + x.min(10)
}

// The guard `m < s.len()` is established, then `m` is rewritten through the
// `&raw const` pointer before the index.
pub fn guard_then_raw_const(s: &[u8], n: usize) -> u8 {
    let mut m = n;
    let p = &raw const m as *mut usize;
    if m < s.len() {
        unsafe {
            *p = usize::MAX;
        }
        s[m]
    } else {
        0
    }
}

// ---- a PARAMETER written through its own `&raw const` slot --------------------
//
// A parameter no statement assigns has its versions collapsed onto its ENTRY value
// (`local_versions_collapse_to_bare`, gated by `place_source_is_stable`). A write
// through `&raw const x as *mut _` changes `x` after the guard, so the collapse
// must be refused, or the guard on the entry value discharges the read of the new
// one — in the body and through a call.

pub fn reseat_raw_const_param(mut x: u8) -> u8 {
    if x < 5 {
        let p = &raw const x as *mut u8;
        unsafe {
            *p = 250;
        }
        x + 10
    } else {
        0
    }
}

pub fn reseat_raw_const_param_index(s: &[u8], mut n: usize) -> u8 {
    if n < s.len() {
        let p = &raw const n as *mut usize;
        unsafe {
            *p = usize::MAX;
        }
        s[n]
    } else {
        0
    }
}

#[inline(never)]
pub fn poke_usize(p: *mut usize) {
    unsafe {
        *p = usize::MAX;
    }
}

pub fn param_written_by_a_call(mut x: u8) -> u8 {
    if x < 5 {
        poke(&raw const x as *mut u8);
        x + 10
    } else {
        0
    }
}

pub fn param_index_written_by_a_call(s: &[u8], mut n: usize) -> u8 {
    if n < s.len() {
        poke_usize(&raw const n as *mut usize);
        s[n]
    } else {
        0
    }
}

// ---- controls: the same programs through `&raw mut` (always listed) ----------

pub fn reseat_raw_mut_loop(a: &mut [u8; 8], i: usize, n: usize) -> u8 {
    let mut s: &mut [u8] = a;
    let p = &raw mut s;
    let mut k = 0usize;
    while k < n {
        unsafe {
            *p = &mut [];
        }
        k += 1;
    }
    if i < 8 { s[i] } else { 0 }
}

pub fn reseat_call_raw_mut_shared(a: &[u8; 8], i: usize) -> u8 {
    let mut s: &[u8] = a;
    reseat_through(&raw mut s, &TWO);
    if i < 8 { s[i] } else { 0 }
}

// ---- the pointee is not the slot: `&raw const (*q)` stays off the list --------
//
// `&raw const (*s)` points at what `s` points to. For a SHARED `s` a write through
// it is UB under both models, so the element fact below must SURVIVE the call
// (the precision control: listing the pointee turns this add row red). For a
// `&mut` `s` the write is defined under Tree Borrows, and it is caught by `s`'s
// own BASE name — `s` is a mutable-pointer local, on the havoc list by its type —
// so the overflow below must stay refuted without listing the pointee.

#[inline(never)]
pub fn observe(p: *const [u8]) {
    let _ = p;
}

pub fn raw_const_pointee_then_call(s: &[u8]) -> u8 {
    let p = &raw const *s;
    if s.len() > 0 && s[0] < 100 {
        observe(p);
        s[0] + 100
    } else {
        0
    }
}

#[inline(never)]
pub fn poke_first(p: *const [u8]) {
    unsafe {
        *(p as *mut u8) = 200;
    }
}

pub fn raw_const_pointee_write_through_mut(s: &mut [u8]) -> u8 {
    let p = &raw const *s;
    if s.len() > 0 && s[0] < 100 {
        poke_first(p);
        s[0] + 100
    } else {
        0
    }
}
