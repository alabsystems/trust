// h1_alias_cast: LAUNDERED-ALIAS-STORE / LAUNDERED-ALIAS-ELIDE-1 (2026-10-11). The
// `al02` shape of h1_alias.rs with an OVERFLOW row, and with the pointer laundered
// WITHOUT an opaque call: a plain `as` cast, `cast_const()`, `wrapping_add(0)`, the
// `&mut len` coercion plus a cast. A store through `p` folds to `len`; a read through
// `q` the referent fold cannot resolve is spelled `q*`, so `*q` before and after the
// store shared one version, the guard bounded the PRE-store value, and the `x + 1`
// row was proved and kernel-certified while every `_bug` below panics at
// `m = usize::MAX, n = 3` (and the advisory build elided its overflow check).
// Every `_bug` panics on that input; every `_ctl` is correct on every input.
// Kept in a file of its own so the line/col anchors of h1_alias.rs do not move.
#![allow(clippy::all, unused_mut, unused_assignments, dead_code)]

#[inline(never)]
pub fn launder(p: *const usize) -> *const usize {
    p
}

// AL07: `q = p as *const usize` (scout `lv3.rs::al_add`).
pub fn al07_cast_store_add_bug(m: usize, n: usize) -> usize {
    let mut len = m;
    let p = &raw mut len;
    let q: *const usize = p as *const usize;
    unsafe {
        let x = *q;
        *p = n;
        if *q > 7 {
            return 0;
        }
        x + 1
    }
}

// AL08: `let p: *mut usize = &mut len` (a coercion), then `q = p as *const usize`
// (scout `lr1.rs::local_ref`).
pub fn al08_local_ref_cast_add_bug(m: usize, n: usize) -> usize {
    let mut len = m;
    let p: *mut usize = &mut len;
    let q = p as *const usize;
    unsafe {
        let x = *q;
        *p = n;
        if *q > 7 {
            return 0;
        }
        x + 1
    }
}

// AL09: `q = p.cast_const()` -- a call result, which the fold never resolves.
pub fn al09_cast_const_add_bug(m: usize, n: usize) -> usize {
    let mut len = m;
    let p = &raw mut len;
    let q = p.cast_const();
    unsafe {
        let x = *q;
        *p = n;
        if *q > 7 {
            return 0;
        }
        x + 1
    }
}

// AL10: `q = p.wrapping_add(0)` -- a call result.
pub fn al10_wrapping_add_add_bug(m: usize, n: usize) -> usize {
    let mut len = m;
    let p = &raw mut len;
    let q = p.wrapping_add(0);
    unsafe {
        let x = *q;
        *p = n;
        if *q > 7 {
            return 0;
        }
        x + 1
    }
}

// AL11: the hazard's own `launder(p)` call with an overflow row (al02's twin).
pub fn al11_launder_call_add_bug(m: usize, n: usize) -> usize {
    let mut len = m;
    let p = &raw mut len;
    let q = launder(p);
    unsafe {
        let x = *q;
        *p = n;
        if *q > 7 {
            return 0;
        }
        x + 1
    }
}

// AL12: the store is a DIRECT write of `len`, not a store through a pointer.
pub fn al12_direct_store_add_bug(m: usize, n: usize) -> usize {
    let mut len = m;
    let p = &raw mut len;
    let q = p.wrapping_add(0);
    unsafe {
        let x = *q;
        len = n;
        if *q > 7 {
            return 0;
        }
        x + 1
    }
}

// AL13: the reverse direction (store through the cast copy `q`, reads through `p`).
// Its check was already kept (scout `lr1.rs::rev_add`): pinned so the fix cannot
// reopen it.
pub fn al13_rev_cast_store_add_bug(m: usize, n: usize) -> usize {
    let mut len = m;
    let p = &raw mut len;
    let q = p as *mut usize;
    unsafe {
        let x = *p;
        *q = n;
        if *p > 7 {
            return 0;
        }
        x + 1
    }
}

// AL14: reads through a cast copy, store through a second copy made by a call
// (scout `lr1.rs::two_cast`). Already kept; pinned.
pub fn al14_two_cast_add_bug(m: usize, n: usize) -> usize {
    let mut len = m;
    let p = &raw mut len;
    let q = p as *const usize;
    let w = p.cast::<usize>();
    unsafe {
        let x = *q;
        *w = n;
        if *q > 7 {
            return 0;
        }
        x + 1
    }
}

// AL15 control: AL07 with the guard BEFORE the store (x = *q <= 7 on every path).
pub fn al15_cast_guard_first_ctl(m: usize, n: usize) -> usize {
    let mut len = m;
    let p = &raw mut len;
    let q: *const usize = p as *const usize;
    unsafe {
        let x = *q;
        if *q > 7 {
            return 0;
        }
        *p = n;
        x + 1
    }
}

// AL16 control: the `p`-only twin -- every read and the store go through `p`, and the
// row reads the post-store value the guard bounds.
pub fn al16_p_only_store_ctl(m: usize, n: usize) -> usize {
    let mut len = m;
    let p = &raw mut len;
    unsafe {
        *p = n;
        if *p > 7 {
            return 0;
        }
        *p + 1
    }
}

// AL17 control: a laundered copy that is only read through (no store at all).
pub fn al17_cast_read_only_ctl(m: usize) -> usize {
    let mut len = m;
    let p = &raw mut len;
    let q = p.wrapping_add(0);
    unsafe {
        if *q > 7 {
            return 0;
        }
        *q + 1
    }
}

// AL18 control: store through `p`, then the guard and the row both read through the
// laundered `q` AFTER the store -- no read straddles it.
pub fn al18_store_then_read_ctl(m: usize, n: usize) -> usize {
    let mut len = m;
    let p = &raw mut len;
    let q = p.wrapping_add(0);
    unsafe {
        *p = n;
        if *q > 7 {
            return 0;
        }
        *q + 1
    }
}

// AL19 (LAUNDERED-ALIAS-CELL-1, wave-24 review, 2026-10-12): the address escapes by a
// SHARED borrow of interior-mutable storage. `Cell::as_ptr(&c)` takes `&c` (no `&mut`,
// no `&raw`), so `c` was no write-channel root and the direct write `c = nc` versioned
// nothing; the `x + 1` row was kernel-certified and the advisory check elided on the
// stage 1 of 51eac007f3 (review `cell.rs` revision `cell_direct`).
pub fn al19_cell_direct_add_bug(m: usize, n: usize) -> usize {
    let mut c = core::cell::Cell::new(m);
    let q = c.as_ptr() as *const usize;
    let nc = core::cell::Cell::new(n);
    unsafe {
        let x = *q;
        c = nc;
        if *q > 7 {
            return 0;
        }
        x + 1
    }
}

// AL20: the whole `Cell` stored through `&c as *const Cell<usize> as *mut Cell<usize>`
// (interior mutation: every byte of a `Cell` is inside its `UnsafeCell`). Before the
// wave-24 `Rvalue::Cast` arm the store was opaque and havocked the list; the arm folds
// `w` to `c`, which no borrow rooted (review `cell2.rs` revision `cell_shared_store`).
#[allow(invalid_reference_casting)]
pub fn al20_cell_cast_store_add_bug(m: usize, n: usize) -> usize {
    let c = core::cell::Cell::new(m);
    let q = c.as_ptr();
    let w = &c as *const core::cell::Cell<usize> as *mut core::cell::Cell<usize>;
    let nc = core::cell::Cell::new(n);
    unsafe {
        let x = *q;
        *w = nc;
        if *q > 7 {
            return 0;
        }
        x + 1
    }
}

// AL21 control: AL19 with the guard BEFORE the write (x = *q <= 7 on every path).
pub fn al21_cell_guard_first_ctl(m: usize, n: usize) -> usize {
    let mut c = core::cell::Cell::new(m);
    let q = c.as_ptr() as *const usize;
    let nc = core::cell::Cell::new(n);
    unsafe {
        let x = *q;
        if *q > 7 {
            return 0;
        }
        c = nc;
        x + 1
    }
}
