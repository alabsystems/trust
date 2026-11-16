//@ needs-trust-verify
//@ edition: 2021
//@ revisions: replace_new replace_old swap_ints max_then_add old_unbounded swap_unbounded reseat reseat_reborrow reseat_alias union_field take_new take_old take_nonzero_then_sub take_old_unbounded
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[replace_new] check-pass
//@[replace_old] check-pass
//@[swap_ints] check-pass
//@[max_then_add] check-fail
//@[old_unbounded] check-fail
//@[swap_unbounded] check-fail
//@[reseat] check-fail
//@[reseat_reborrow] check-fail
//@[reseat_alias] check-fail
//@[union_field] check-fail
//@[take_new] check-pass
//@[take_old] check-pass
//@[take_nonzero_then_sub] check-fail
//@[take_old_unbounded] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//! Trust (2026-10-05, MEM_REPLACE_SWAP): the exact effect of `mem::replace` and
//! `mem::swap` on the places their `&mut` arguments borrow
//! (`generate::call_facts::mem_replace_swap_facts`).
//!
//! # Before (measured on the stage 1 of `480b31abee`, 2026-10-05)
//!
//! `replace_new` and `replace_old`: the `+ 1` was `[overflow:add] FAILED` (the place and
//! the returned value were unconstrained after the call).
//!
//! # The refused rails, each a program that really panics
//!
//! * `max_then_add` — `replace(&mut x, u32::MAX)` then `x + 1`.
//! * `old_unbounded` — the returned old value of an unbounded `x`, plus one.
//! * `swap_unbounded` — `swap(&mut a, &mut b)` with `a` bounded and `b` not; `a + 1`.
//! * `reseat` — the false proof the 2026-10-05 review found in the first version: the
//!   argument block reseats `r` after `&mut *r` is taken, so `*r` afterwards is `*s`,
//!   which the call never wrote (`reseat(&mut 0, &mut u32::MAX)` panics).
//! * `reseat_reborrow`, `reseat_alias` — the two the re-review found once a one-value
//!   `Deref` base was admitted: the pointer a reborrow folds to is reseated, and the base
//!   is reseated through a raw alias. Places behind a `Deref` are no longer modeled.
//! * `union_field` — the false proof the final review found: `u.b = x` overwrites the bytes
//!   of `u.a`, which the versioning treats as independent (`union_field(u32::MAX)`
//!   panics). Only whole locals are modeled now.
//!
//! # `mem::take` (2026-10-05)
//!
//! `take(&mut P)` is `replace(&mut P, T::default())`, modeled only where the default is
//! exact: an integer's `0` (and a std `Vec`'s length `0`). Before (measured on the sealed
//! `trustc 0.10.0+g4d9a20e3d`, 2026-10-05), both were rejected: `take_new` with a failed
//! `+ 1` overflow row, `take_old` with it unknown. Rails:
//!
//! * `take_nonzero_then_sub` — `x != 0`, `take(&mut x)`, then `x - 1`: the place is `0`
//!   afterwards, so the subtraction really underflows. A model that left `x` at its old
//!   value would prove it.
//! * `take_old_unbounded` — the returned old value of an unbounded `x`, plus one.

#[cfg(replace_new)]
pub fn replace_new(mut x: u32) -> u32 {
    let _old = std::mem::replace(&mut x, 5);
    x + 1
}

#[cfg(replace_old)]
pub fn replace_old(mut x: u32) -> u32 {
    if x > 10 {
        return 0;
    }
    let old = std::mem::replace(&mut x, 5);
    old + 1
}

#[cfg(swap_ints)]
pub fn swap_ints(mut a: u32, mut b: u32) -> u32 {
    if b > 10 {
        return 0;
    }
    std::mem::swap(&mut a, &mut b);
    a + 1
}

#[cfg(max_then_add)]
pub fn max_then_add(mut x: u32) -> u32 {
    let _old = std::mem::replace(&mut x, u32::MAX);
    x + 1
}

#[cfg(old_unbounded)]
pub fn old_unbounded(mut x: u32) -> u32 {
    let old = std::mem::replace(&mut x, 5);
    old + 1
}

#[cfg(swap_unbounded)]
pub fn swap_unbounded(mut a: u32, mut b: u32) -> u32 {
    if a > 10 {
        return 0;
    }
    std::mem::swap(&mut a, &mut b);
    a + 1
}

#[cfg(reseat)]
pub fn reseat<'a>(mut r: &'a mut u32, s: &'a mut u32) -> u32 {
    let _old = std::mem::replace(&mut *r, {
        r = s;
        5
    });
    *r + 1
}

#[cfg(reseat_reborrow)]
pub fn reseat_reborrow<'a>(mut q: &'a mut u32, s: &'a mut u32) -> u32 {
    let r = &mut *q;
    let _old = std::mem::replace(&mut *r, {
        q = s;
        5
    });
    *q + 1
}

#[cfg(reseat_alias)]
pub fn reseat_alias<'a>(mut r: &'a mut u32, s: &'a mut u32) -> u32 {
    let pr: *mut &'a mut u32 = &raw mut r;
    let _old = std::mem::replace(&mut *r, {
        unsafe {
            *pr = s;
        }
        5
    });
    *r + 1
}

#[cfg(union_field)]
pub union U {
    a: u32,
    b: u32,
}

#[cfg(union_field)]
pub fn union_field(x: u32) -> u32 {
    let mut u = U { b: 0 };
    u.a = 0;
    u.b = x;
    let old = std::mem::replace(unsafe { &mut u.a }, 5);
    old + 1
}

#[cfg(take_new)]
pub fn take_new(mut x: u32) -> u32 {
    let _old = std::mem::take(&mut x);
    x + 1
}

#[cfg(take_old)]
pub fn take_old(mut x: u32) -> u32 {
    if x > 10 {
        return 0;
    }
    let old = std::mem::take(&mut x);
    old + 1
}

#[cfg(take_nonzero_then_sub)]
pub fn take_nonzero_then_sub(mut x: u32) -> u32 {
    if x == 0 {
        return 0;
    }
    let _old = std::mem::take(&mut x);
    x - 1
}

#[cfg(take_old_unbounded)]
pub fn take_old_unbounded(mut x: u32) -> u32 {
    let old = std::mem::take(&mut x);
    old + 1
}
