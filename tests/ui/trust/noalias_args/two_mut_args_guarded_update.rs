//@ needs-trust-verify
//@ edition: 2021
//@ revisions: guarded raw reseat not_unpin generic field_reached caller_spends zero_row_caller zero_row_callee_certify stored_pointer premise_row per_row touched
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[caller_spends] compile-flags: -Ztrust-policy=certify
//@[zero_row_caller] compile-flags: -Ztrust-policy=certify
//@[zero_row_callee_certify] compile-flags: -Ztrust-policy=certify
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[guarded] check-pass
//@[raw] check-fail
//@[reseat] check-fail
//@[not_unpin] check-fail
//@[generic] check-fail
//@[field_reached] check-fail
//@[caller_spends] check-fail
//@[zero_row_caller] check-pass
//@[zero_row_callee_certify] check-pass
//@[stored_pointer] check-fail
//@[premise_row] check-pass
//@[per_row] check-pass
//@[touched] check-pass
//@[stored_pointer] forbid-output: aliasing premise
//@[premise_row] forbid-output: kernel-certified by the clean CIC kernel
//! D15 NOALIAS_MUT_ARGS (2026-10-08): two `&mut T` arguments (`T: Unpin`) live for
//! the whole call never overlap, so a store through one keeps the facts about the
//! other. `guarded` holds the ordinary-Rust sweep's m06/m07/m04/p26 shapes, each
//! refused before (the store through `a` havocked the guard on `*n`). The premise is
//! disclosed and no caller spends the verdict (`caller_spends`, under `certify`, must
//! stay refused: `bump`'s verdict does not discharge its call). Rows are graded one by
//! one (2026-10-17, gate RCA "premise"): a row whose VC the premise shaped is demoted
//! (`premise_row`: `bump`'s one row needs the guard only the premise keeps, so no row
//! there is kernel-certified, `forbid-output`); a row whose VC the premise-free
//! generation reproduces byte for byte keeps its kernel certificate (`per_row`: of
//! `mixed`'s two rows, the `(x & 0x7f) + 1` overflow that reads no argument; in
//! `guarded`, the constant-index bounds rows of `m07` and `m04`, checked before any
//! store). Until 2026-10-17 every row of such a body was demoted. `touched`: a row
//! whose VC the premise changed without needing it (`rect[2] = old` carries
//! `old = rect[1]` across the store through `uv` only under the premise) dispatches
//! its premise-free twin, which the interval lane proves, and is certified too
//! (`aterm_gpu::renderer::clip_textured_quad_x`'s shape, `f32` elements as there:
//! with `u32` elements the interval lane declines that twin, and a twin it does not
//! prove is never dispatched, so that row stays premised and demoted).
//!
//! Each other revision is outside the premise and must stay refused: a raw pointer
//! made from the argument, an argument reseated in the body, a `!Unpin` pointee, a
//! generic `T` not known `Unpin`, and `&mut` reached through a struct field.
//! `zero_row_caller` and `zero_row_callee_certify` (review rounds 81-82): a body with
//! NO obligations has no verdict that could rest on the premise (obligations are
//! minted per operation; the premise only changes which facts later discharge them),
//! so its marker is cleared, it keeps its zero-obligation blessing, and its caller
//! passes `certify` exactly as before D15.
//! `stored_pointer` (review round 83): `noalias` covers `*b`, not memory reached
//! through a pointer STORED in `*b`, so an argument whose pointee holds a pointer
//! gets no premise at all (`*b.p` aliases `*a` here; the overflow really happens).

#[cfg(guarded)]
pub fn m06(a: &mut u32, n: &mut usize) {
    //[guarded]~^ NOTE Trust aliasing premise NOALIAS_MUT_ARGS
    if *n < 8 {
        *a = 1;
        *n += 1;
    }
}

#[cfg(guarded)]
pub fn m07(a: &mut [u32; 8], n: &mut usize) {
    //[guarded]~^ NOTE of which 1 kernel-certified by the clean CIC kernel
    if *n < 8 {
        a[0] = 1;
        *n += 1;
    }
}

#[cfg(guarded)]
pub fn m04(items: &mut [u32; 8], len: &mut usize, x: u32) {
    //[guarded]~^ NOTE of which 1 kernel-certified by the clean CIC kernel
    if *len < 8 {
        items[0] = x;
        *len += 1;
    }
}

#[cfg(guarded)]
pub struct Account {
    pub balance: u32,
}

#[cfg(guarded)]
pub fn p26(from: &mut Account, to: &mut Account, amt: u32) -> bool {
    if from.balance >= amt && to.balance <= u32::MAX - amt {
        from.balance -= amt;
        to.balance += amt;
        true
    } else {
        false
    }
}

#[cfg(raw)]
pub fn f(a: &mut u32, n: &mut usize) {
    if *n < 8 {
        let p = a as *mut u32;
        unsafe { *p = 1 };
        *n += 1;
    }
}

#[cfg(reseat)]
pub fn f<'a>(mut a: &'a mut usize, n: &'a mut usize, o: &'a mut usize) {
    if *n < 8 {
        a = o;
        *a = 1;
        *n += 1;
    }
}

#[cfg(not_unpin)]
pub struct Pinned {
    pub x: usize,
    _p: std::marker::PhantomPinned,
}

#[cfg(not_unpin)]
pub fn f(a: &mut Pinned, n: &mut Pinned) {
    if n.x < 8 {
        a.x = 1;
        n.x += 1;
    }
}

#[cfg(generic)]
pub fn f<T>(a: &mut T, v: T, n: &mut usize) {
    if *n < 8 {
        *a = v;
        *n += 1;
    }
}

#[cfg(field_reached)]
pub struct Two<'a> {
    pub a: &'a mut usize,
    pub n: &'a mut usize,
}

#[cfg(field_reached)]
pub fn f(t: Two<'_>) {
    if *t.n < 8 {
        *t.a = 1;
        *t.n += 1;
    }
}

#[cfg(caller_spends)]
pub fn bump(a: &mut u32, n: &mut usize) {
    if *n < 8 {
        *a = 1;
        *n += 1;
    }
}

#[cfg(caller_spends)]
pub fn f(x: &mut u32, y: &mut usize) {
    bump(x, y);
}

#[cfg(zero_row_caller)]
pub fn g(a: &mut u32, n: &mut usize) {
    if *n < 8 {
        *a = 1;
        let k = *n;
        h(k);
    }
}

#[cfg(zero_row_caller)]
pub fn h(k: usize) -> usize {
    k
}

#[cfg(zero_row_caller)]
pub fn f(x: &mut u32, y: &mut usize) {
    g(x, y);
}

#[cfg(zero_row_callee_certify)]
fn sett(a: &mut u32, n: &mut u32, c: bool) {
    if c {
        *a = 1;
    }
    *n = 2;
}

#[cfg(zero_row_callee_certify)]
pub fn f(x: &mut u32, y: &mut u32) -> u32 {
    sett(x, y, true);
    5
}

#[cfg(stored_pointer)]
pub struct W {
    p: *mut u8,
}

#[cfg(stored_pointer)]
pub fn f(a: &mut u8, b: &mut W) -> u8 {
    b.p = a as *mut u8;
    let v = unsafe { *b.p };
    if v < 8 {
        *a = 250;
        let w = unsafe { *b.p };
        w + 10
    } else {
        0
    }
}

#[cfg(premise_row)]
pub fn bump(a: &mut u32, n: &mut usize) {
    //[premise_row]~^ NOTE Trust aliasing premise NOALIAS_MUT_ARGS
    if *n < 8 {
        *a = 1;
        *n += 1;
    }
}

#[cfg(per_row)]
pub fn mixed(a: &mut u32, n: &mut usize, x: u8) -> u8 {
    //[per_row]~^ NOTE Trust aliasing premise NOALIAS_MUT_ARGS
    //[per_row]~| NOTE of which 1 kernel-certified by the clean CIC kernel
    let y = (x & 0x7f) + 1;
    if *n < 8 {
        *a = 1;
        *n += 1;
    }
    y
}

#[cfg(touched)]
pub fn touched(rect: &mut [f32; 4], uv: &mut [f32; 4]) -> bool {
    //[touched]~^ NOTE Trust aliasing premise NOALIAS_MUT_ARGS
    //[touched]~| NOTE of which 3 kernel-certified by the clean CIC kernel
    let old = rect[1];
    uv[0] = old;
    rect[2] = old;
    true
}
