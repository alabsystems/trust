// adv_cell: writes the statement-version oracle may not attribute to a local -- interior
// mutability (Cell / UnsafeCell, NOT UB) and a `&raw const` pointer cast to `*mut`
// (aliasing-model dependent) -- feeding an ordinary index row and a range row.
// Every `_bug` panics on the input in its comment; every `_ctl` is correct.
#![allow(clippy::all, unused_mut, unused_assignments, dead_code)]
use std::cell::{Cell, UnsafeCell};

// CE01: Cell local: get, set(+4), index with the new value.  n=0 panics (index 4).
pub fn ce01_cell_set_index_bug(n: usize, t: &[u8; 4]) -> u8 {
    let c = Cell::new(n & 3);
    let k0 = c.get();
    c.set(k0 + 4);
    t[c.get()]
}

// CE02: UnsafeCell local: write through `get()`, read back with `into_inner()`.
// n=0 panics (index 4).
pub fn ce02_unsafecell_write_into_inner_bug(n: usize, t: &[u8; 4]) -> u8 {
    let c = UnsafeCell::new(n & 3);
    let p = c.get();
    unsafe { *p += 4 };
    t[c.into_inner()]
}

// CE03: UnsafeCell local field read DIRECTLY through a second `get()` pointer.
// n=0 panics (index 4).
pub fn ce03_unsafecell_two_ptrs_bug(n: usize, t: &[u8; 4]) -> u8 {
    let c = UnsafeCell::new(n & 3);
    let w = c.get();
    let r = c.get() as *const usize;
    unsafe {
        *w += 4;
        t[*r]
    }
}

// CE04: Cell range bound (H1 x interior mutability): range built from the old value,
// guard on the new one.  m=100, n=3 panics.
pub fn ce04_cell_range_stale_bug(buf: &[u8; 8], m: usize, n: usize) -> usize {
    let c = Cell::new(m);
    let r = ..c.get();
    c.set(n);
    if c.get() > 8 {
        return 0;
    }
    buf[r].len()
}

// CE05: guard on a Cell's value, then the cell is changed through a SHARED reference
// handed to a helper that is inlined at -O1.  n=0 panics (index 4).
#[inline(always)]
fn bump(c: &Cell<usize>) {
    c.set(c.get() + 4);
}
pub fn ce05_cell_shared_helper_bug(n: usize, t: &[u8; 4]) -> u8 {
    let c = Cell::new(n & 3);
    if c.get() >= 4 {
        return 0;
    }
    bump(&c);
    t[c.get()]
}

// CE06: `&raw const k` cast to `*mut` and written (Tree Borrows: allowed; Stacked
// Borrows: UB), then a guard-free index of `k`.  n=0 panics (index 4).
pub fn ce06_raw_const_store_index_bug(n: usize, t: &[u8; 4]) -> u8 {
    let mut k = n & 3;
    let p = &raw const k;
    unsafe { *(p as *mut usize) += 4 };
    t[k]
}

// CE07: control: Cell set to a SAFE value.
pub fn ce07_cell_safe_ctl(n: usize, t: &[u8; 4]) -> u8 {
    let c = Cell::new(n & 3);
    c.set((c.get() + 1) & 3);
    t[c.get()]
}
