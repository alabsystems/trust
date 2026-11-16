// Counter-programs for the memory a pointer this function never retagged can
// reach — a raw pointer anywhere, or a `&mut` or `Box` STORED in memory behind a
// reference — and for the calls that may write it. Any code holding a copy of such a
// pointer, or a raw pointer derived from it, can write its target, and a callee with
// no argument at all reaches a copy stashed before the call (`G` below, set by the
// caller's caller). That write is defined under Stacked Borrows and Tree Borrows
// alike: a raw pointer is not retagged; a reference protects the bytes it covers
// (`&PW`, `&mut PW`, `&mut BW`, `&MW`), not what a pointer stored in them points to;
// and a `&mut` stored in memory is not retagged when this function reads through it,
// so a raw pointer derived from it earlier stays a valid child (reads through the
// parent do not invalidate it). A `&mut` PARAMETER is different: its entry retag
// pops (Tree Borrows: disables, under a protector) every alias derived before it.
//
// docs/TCB.md's "Pure-value arguments reach no caller local" row lets a call whose
// arguments are all pointer-free values kill only its destination. That premise is
// about caller LOCALS (a non-`'static` `&mut` cannot be stashed by safe code, and a
// laundered address needs an in-body `&raw` or raw cast, which turns the skip off);
// the memory above is not a caller local. The whole-function havoc list, which every
// other call kills, named a raw pointer or `Box` reached through a `&` but not a
// `&mut` stored there. So the targets' facts must die at such calls, and the facts
// about the bytes a reference covers must not.
//
// Every `stash_*` body indexes after `poke_global` set the pointee to `usize::MAX`
// and panics natively (`index out of bounds: the len is 4 but the index is
// 18446744073709551615`, -O0 and -O3, `-C overflow-checks=on`) when `G` aliases it.
// The `*_keeps_*` bodies are PRECISION controls, the shapes the skip exists for: a
// scalar the callee cannot reach (a field beside the pointer behind `&mut`, a
// parameter) keeps its fact across the call. They do not panic.
//
// The MIR is dumped with `-Zub-checks=no` (what a build without debug assertions
// gets): with UB checks on, the alignment check's cast to a raw pointer is a
// laundering site (`func_has_pointer_laundering`) that turns the skip off for the
// whole body, and every counter-program refutes for that reason alone.
//
// Fixtures: tests/fixtures/raw_pointee_across_pure_value_call_<fn>_mir.json (a
// closure body `f::{closure#0}` is saved as `f_closure0`), dumped from this file by
// Trust `main` stage 1 a7ea88986d with
//   rustc --edition 2024 --crate-type lib -Ztrust-verify-profile=unix_hardened \
//         -Ztrust-policy=advisory -Zub-checks=no -Ztrust-dump=mir:<dir> \
//         crates/trust-vcgen/tests/data/raw_pointee_across_pure_value_call.rs
// run from the repository root (so `span.file` is already repo-relative; nothing
// in the dumps was edited).
#![allow(static_mut_refs, dead_code, unused_unsafe)]

/// A copy of the pointer the caller's caller stashed before the call.
pub static mut G: *mut usize = core::ptr::null_mut();

/// Takes no argument; writes through the stashed copy.
#[inline(never)]
pub fn poke_global() {
    unsafe {
        *G = usize::MAX;
    }
}

/// Takes one pointer-free value; writes it through the stashed copy.
#[inline(never)]
pub fn poke_global_with(v: usize) {
    unsafe {
        *G = v;
    }
}

pub struct PW {
    pub p: *mut usize,
}

// An owned raw-pointer parameter.
pub fn stash_raw_param(s: &[u8], m: *mut usize) -> u8 {
    let i = unsafe { *m };
    if i < s.len() {
        poke_global();
        s[unsafe { *m }]
    } else {
        0
    }
}

// The same across a call handed a pointer-free VALUE (a constant).
pub fn stash_raw_param_value_arg(s: &[u8], m: *mut usize) -> u8 {
    let i = unsafe { *m };
    if i < s.len() {
        poke_global_with(usize::MAX);
        s[unsafe { *m }]
    } else {
        0
    }
}

// A raw pointer behind a SHARED reference (`w*.0`).
pub fn stash_shared_ref(s: &[u8], w: &PW) -> u8 {
    let i = unsafe { *w.p };
    if i < s.len() {
        poke_global();
        s[unsafe { *w.p }]
    } else {
        0
    }
}

// A raw pointer behind a MUTABLE reference (`w*.0`): `&mut PW` protects the bytes of
// the `PW`, not what its pointer points to.
pub fn stash_mut_ref(s: &[u8], w: &mut PW) -> u8 {
    let i = unsafe { *w.p };
    if i < s.len() {
        poke_global();
        s[unsafe { *w.p }]
    } else {
        0
    }
}

pub struct BW {
    pub b: Box<usize>,
}

// A `Box` behind a MUTABLE reference, whose pointee the caller's caller stashed a raw
// pointer to (`G = &raw mut *bw.b`). The `&mut BW` protects the `Box`'s pointer
// bytes, not its pointee. (A `Box` PARAMETER would not do: it is retagged and
// protected at entry under both models, so the stashed write would be UB.)
pub fn stash_box_behind_mut_ref(s: &[u8], w: &mut BW) -> u8 {
    if *w.b < s.len() {
        poke_global();
        s[*w.b]
    } else {
        0
    }
}

pub struct MW<'a> {
    pub r: &'a mut usize,
}

// A `&mut` STORED behind a `&mut` (`w*.0`). The function's entry retag protects the
// bytes of the `MW` (the inner reference's pointer), not its target, and the inner
// reference is never retagged here: a raw pointer the caller's caller derived from
// it (`G = &raw mut *r`, then `MW { r }`) stays a valid child, and its write is
// defined under both models — reads through the parent do not invalidate it.
pub fn stash_mut_ref_behind_mut_ref(s: &[u8], w: &mut MW) -> u8 {
    let i = *w.r;
    if i < s.len() {
        poke_global();
        s[*w.r]
    } else {
        0
    }
}

// The same `&mut` stored behind a SHARED reference (`w*.0`): `& &mut usize` cannot
// write through the `&`, but the stashed child can.
pub fn stash_mut_ref_behind_shared_ref(s: &[u8], w: &MW) -> u8 {
    let i = *w.r;
    if i < s.len() {
        poke_global();
        s[*w.r]
    } else {
        0
    }
}

/// Takes a reference (so the call is NOT a pure-value call); writes through the
/// stashed copy.
#[inline(never)]
pub fn poke_global_ref(x: &usize) {
    let _ = *x;
    unsafe {
        *G = usize::MAX;
    }
}

// The `&mut`-behind-`&` shape across a call that receives a pointer (`&i`), so the
// whole-function havoc list applies, not the pure-value skip.
pub fn stash_mut_ref_behind_shared_ref_pointer_arg(s: &[u8], w: &MW) -> u8 {
    let i = *w.r;
    if i < s.len() {
        poke_global_ref(&i);
        s[*w.r]
    } else {
        0
    }
}

// A closure body (`Fn`, so `_1: &{closure}`) whose capture is a `*mut usize`.
pub fn stash_closure_capture(s: &[u8], m: *mut usize) -> u8 {
    let f = move |t: &[u8]| -> u8 {
        let i = unsafe { *m };
        if i < t.len() {
            poke_global();
            t[unsafe { *m }]
        } else {
            0
        }
    };
    f(s)
}

pub struct PN {
    pub p: *mut usize,
    pub n: usize,
}

// PRECISION: `w.n` sits in the bytes `&mut PN` protects; a callee with no argument
// cannot write it, so `w.n < 8` still bounds `s[w.n]` across the call. The pointer
// beside it is what the havoc must name, never `w`.
pub fn mut_ref_scalar_keeps_its_fact(s: &[u8; 8], w: &mut PN) -> u8 {
    if w.n < 8 {
        poke_global();
        s[w.n]
    } else {
        0
    }
}

pub struct BN {
    pub b: Box<usize>,
    pub n: usize,
}

// PRECISION: the same beside a `Box`.
pub fn mut_ref_scalar_beside_a_box_keeps_its_fact(s: &[u8; 8], w: &mut BN) -> u8 {
    if w.n < 8 {
        poke_global();
        s[w.n]
    } else {
        0
    }
}

pub struct MN<'a> {
    pub r: &'a mut usize,
    pub n: usize,
}

// PRECISION: the same beside a `&mut` stored in the pointee.
pub fn mut_ref_scalar_beside_a_stored_mut_ref_keeps_its_fact(s: &[u8; 8], w: &mut MN) -> u8 {
    if w.n < 8 {
        poke_global();
        s[w.n]
    } else {
        0
    }
}

// PRECISION: a `&mut` PARAMETER's own target is protected for the whole call (its
// entry retag pops, or under Tree Borrows disables, every alias derived before it),
// so `*r < 8` still bounds `s[*r]` across a call with no pointer argument.
pub fn mut_ref_param_target_keeps_its_fact(s: &[u8; 8], r: &mut usize) -> u8 {
    if *r < 8 {
        poke_global();
        s[*r]
    } else {
        0
    }
}

// PRECISION: a scalar parameter in a body that also holds a raw pointer.
pub fn scalar_param_keeps_its_fact(s: &[u8], m: *mut usize, i: usize) -> u8 {
    let _ = unsafe { *m };
    if i < s.len() {
        poke_global();
        s[i]
    } else {
        0
    }
}
