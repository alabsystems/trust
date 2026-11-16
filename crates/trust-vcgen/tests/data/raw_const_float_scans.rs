// Counter-programs for the FLOAT lane's stability scans: a float the lane bounds
// (a literal, a contract-bounded parameter field, an abs-guarded field, a
// call-initialised element) is written through a `&raw const` pointer cast to
// `*mut`, and the bounded op then overflows to infinity. Each body returns `inf`
// natively (-O0 and -O3). The float lane decides `FloatOverflowToInfinity` by
// interval tracing and, when it bounds the result, emits NO obligation at all, so
// a stale bound here does not prove a row — it removes it.
//
// The scans (`float_whole_local_defs`, `param_place_is_entry_stable`, the
// masked-element lane) counted `&mut` / `&raw mut` as write channels and missed
// `&raw const`. Tree Borrows accepts a write through `&raw const x as *mut _`
// (Stacked Borrows rejects it), and Trust assumes only what both models validate.
// Every binding written that way below is `mut` (or is reached through `&mut`):
// the Rust Reference lists mutating bytes owned by an immutable binding as UB.
//
// Fixtures: tests/fixtures/raw_const_float_scans_<fn>_mir.json, dumped from this
// file by Trust `main` stage 1 a7ea88986d with
//   rustc --edition 2024 --crate-type lib -Ztrust-verify-profile=unix_hardened \
//         -Ztrust-policy=advisory -Ztrust-dump=mir:<dir> \
//         crates/trust-vcgen/tests/data/raw_const_float_scans.rs
// run from the repository root (nothing in the dumps was edited).
#![allow(unused_mut)]

#[inline(never)]
pub fn poke_f64(p: *mut f64) {
    unsafe {
        *p = f64::MAX;
    }
}

#[inline(never)]
pub fn poke_f32(p: *mut f32) {
    unsafe {
        *p = f32::MAX;
    }
}

// ---- a float LOCAL (`float_whole_local_defs`) -----------------------------------

// `v`'s only visible def is `2.0`, so `v * 4.0` was bounded by `8.0`.
pub fn float_local_written_directly() -> f64 {
    let mut v: f64 = 2.0;
    let p = &raw const v as *mut f64;
    unsafe {
        *p = f64::MAX;
    }
    v * 4.0
}

pub fn float_local_written_by_a_call() -> f64 {
    let mut v: f64 = 2.0;
    poke_f64(&raw const v as *mut f64);
    v * 4.0
}

pub fn f32_local_written_by_a_call() -> f32 {
    let mut v: f32 = 1.0;
    poke_f32(&raw const v as *mut f32);
    v + f32::MAX
}

// CONTROL: the channel the scans always named. The row exists before and after.
pub fn float_local_written_through_raw_mut() -> f64 {
    let mut v: f64 = 2.0;
    poke_f64(&raw mut v);
    v * 4.0
}

// ---- a contract-bounded PARAMETER (`param_place_is_entry_stable`) ---------------
//
// A read of `s.0` takes the projected-place path (`contract_range`), which trusts
// the ENTRY bound only while the parameter is entry-stable; the body rewrites `s`
// through `&raw const s`. (A `&raw const` of a FIELD, `&raw const s.0`, never
// reaches the verifier today: the extractor refuses that MIR shape as an
// `[addr-of-field]` assumption, so the whole parameter is taken here.)

pub struct P2(pub f64, pub f64);

#[inline(never)]
pub fn poke_p2(p: *mut P2) {
    unsafe {
        (*p).0 = f64::MAX;
    }
}

#[trust::requires(s.0 <= 2.0 && s.0 >= -2.0)]
pub fn contract_bounded_param_written_through_raw_const(mut s: P2) -> f64 {
    poke_p2(&raw const s as *mut P2);
    s.0 * 4.0
}

impl P2 {
    #[trust::requires(self.0 <= 2.0 && self.0 >= -2.0)]
    pub fn contract_bounded_self_written_through_raw_const(mut self) -> f64 {
        poke_p2(&raw const self as *mut P2);
        self.0 * 4.0
    }
}

// ---- a parameter's POINTEE (the abs-guard base, `float_whole_local_defs`) --------
//
// `&raw const *s` has a `Deref`: it is not a slot of this frame, so the slot-write
// rule rightly leaves it off the havoc list (`s`'s base name covers it there). The
// abs-guard lane asks a different question — is the memory `s` POINTS TO the same
// at the abs read and at the division — and a write through that pointer (derived
// from `&mut`, so defined under Tree Borrows) changes it.

#[inline(never)]
pub fn poke_tiny(p: *mut f64) {
    unsafe {
        *p = 1.0e-310;
    }
}

// The abs guard `|*s| > 1e-20` floors the divisor; the body then makes it tiny.
pub fn abs_guarded_pointee_written_through_raw_const(s: &mut f64) -> f64 {
    if s.abs() > 1.0e-20 {
        poke_tiny(&raw const *s as *mut f64);
        1.0 / *s
    } else {
        0.0
    }
}

// ---- a call-initialised aggregate's ELEMENT (the masked-element lane) -----------
//
// The projected store `m.c[1] = 3.0` poisons the whole-local def model, so only
// the masked-element lane (one Call init, no aliasing store reaching the read) can
// bound `m.c[0]` — and a callee writing through `&raw const m` is such a store.

pub struct Cols {
    pub c: [f64; 2],
}

#[inline(never)]
pub fn make_cols() -> Cols {
    Cols { c: [1.0, 2.0] }
}

#[inline(never)]
pub fn poke_cols(p: *mut Cols) {
    unsafe {
        (*p).c[0] = f64::MAX;
    }
}

pub fn masked_element_written_by_a_call() -> f64 {
    let mut m = make_cols();
    m.c[1] = 3.0;
    poke_cols(&raw const m as *mut Cols);
    m.c[0] * 4.0
}
