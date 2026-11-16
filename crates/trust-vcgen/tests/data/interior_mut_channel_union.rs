// INTERIOR-MUT-CHANNEL-1 on real, UNEDITED rustc MIR (`tests/interior_mut_channel_union_realmir.rs`).
// A union read through its plain field `n: u32` beside a cell field: rustc reads `u.n`
// as a PLACE, so no `Cell::get` call hides the read and no hand edit is needed. A call
// handed `&u` (or `&u.c`, or nothing, given a parked `&'static`) sets the cell to
// `u32::MAX` with defined behaviour, so `u.n + 1` overflows although the guard
// `u.n < 100` held before the call.
//
// Every `must_refute_*` panics natively (`attempt to add with overflow`) at -O0, and at
// -O3 with `-C overflow-checks=on`, on the input in its comment. Every `control_*`
// returns normally on the same input: the read is guarded after the call, nothing can
// write the bytes, or the add cannot overflow.
#![allow(clippy::all, unused_unsafe, dead_code)]
use std::cell::{Cell, UnsafeCell};
use std::mem::{ManuallyDrop, MaybeUninit};
use std::sync::atomic::{AtomicU32, Ordering};

#[repr(C)]
pub union U32 {
    pub c: ManuallyDrop<Cell<u32>>,
    pub n: u32,
}
#[inline(never)]
pub fn poke(u: &U32) {
    unsafe { u.c.set(u32::MAX) }
}
#[inline(never)]
pub fn poke_cell(c: &Cell<u32>) {
    c.set(u32::MAX);
}

// i = 0. The union by value (the review's q04).
pub fn must_refute_owned_union(i: u32) -> u32 {
    let u = U32 { n: i };
    if unsafe { u.n } < 100 {
        poke(&u);
        (unsafe { u.n }) + 1
    } else {
        0
    }
}

// u = &U32 { n: 0 }. The union behind `&` (the review's q05).
pub fn must_refute_union_ref(u: &U32) -> u32 {
    if unsafe { u.n } < 100 {
        poke(u);
        (unsafe { u.n }) + 1
    } else {
        0
    }
}

// i = 0. The call is handed the cell field itself (`&*u.c`, through `ManuallyDrop::deref`).
pub fn must_refute_owned_union_cell_field_borrow(i: u32) -> u32 {
    let u = U32 { n: i };
    if unsafe { u.n } < 100 {
        poke_cell(unsafe { &u.c });
        (unsafe { u.n }) + 1
    } else {
        0
    }
}

// u = &U32 { n: 0 }. The cell field of a union behind `&`.
pub fn must_refute_union_ref_cell_field_borrow(u: &U32) -> u32 {
    if unsafe { u.n } < 100 {
        poke_cell(unsafe { &u.c });
        (unsafe { u.n }) + 1
    } else {
        0
    }
}

pub struct H {
    pub k: u32,
    pub u: U32,
}
#[inline(never)]
pub fn poke_h(h: &H) {
    unsafe { h.u.c.set(u32::MAX) }
}

// i = 0. A union field of an owned struct, the call handed `&h.u`.
pub fn must_refute_owned_struct_union_field(i: u32) -> u32 {
    let h = H { k: 1, u: U32 { n: i } };
    if unsafe { h.u.n } < 100 {
        poke(&h.u);
        (unsafe { h.u.n }) + 1
    } else {
        0
    }
}

// h = &H { k: 1, u: U32 { n: 0 } }. A union field of a struct behind `&`.
pub fn must_refute_struct_union_field_ref(h: &H) -> u32 {
    if unsafe { h.u.n } < 100 {
        poke_h(h);
        (unsafe { h.u.n }) + 1
    } else {
        0
    }
}

// i = 0. The cell field of a union field of an owned struct, `&*h.u.c`.
pub fn must_refute_owned_struct_union_cell_field_borrow(i: u32) -> u32 {
    let h = H { k: 1, u: U32 { n: i } };
    if unsafe { h.u.n } < 100 {
        poke_cell(unsafe { &h.u.c });
        (unsafe { h.u.n }) + 1
    } else {
        0
    }
}

#[repr(C)]
pub union UU32 {
    pub c: ManuallyDrop<UnsafeCell<u32>>,
    pub n: u32,
}
#[inline(never)]
pub fn poke_uu(u: &UU32) {
    unsafe { *u.c.get() = u32::MAX }
}

// i = 0. The cell field is a bare `UnsafeCell`.
pub fn must_refute_owned_unsafecell_union(i: u32) -> u32 {
    let u = UU32 { n: i };
    if unsafe { u.n } < 100 {
        poke_uu(&u);
        (unsafe { u.n }) + 1
    } else {
        0
    }
}

#[repr(C)]
pub union UA32 {
    pub c: ManuallyDrop<AtomicU32>,
    pub n: u32,
}
#[inline(never)]
pub fn poke_ua(u: &UA32) {
    unsafe { u.c.store(u32::MAX, Ordering::Relaxed) }
}

// i = 0. The cell field is an atomic.
pub fn must_refute_owned_atomic_union(i: u32) -> u32 {
    let u = UA32 { n: i };
    if unsafe { u.n } < 100 {
        poke_ua(&u);
        (unsafe { u.n }) + 1
    } else {
        0
    }
}

#[repr(C)]
pub union UM32 {
    pub c: ManuallyDrop<MaybeUninit<Cell<u32>>>,
    pub n: u32,
}
#[inline(never)]
pub fn poke_um(u: &UM32) {
    unsafe { u.c.assume_init_ref().set(u32::MAX) }
}

// i = 0. The cell sits inside a `MaybeUninit` (itself a union).
pub fn must_refute_owned_maybe_uninit_cell_union(i: u32) -> u32 {
    let u = UM32 { n: i };
    if unsafe { u.n } < 100 {
        poke_um(&u);
        (unsafe { u.n }) + 1
    } else {
        0
    }
}

thread_local! {
    static PARKED: Cell<Option<&'static U32>> = const { Cell::new(None) };
}
#[inline(never)]
pub fn park(u: &'static U32) {
    PARKED.with(|p| p.set(Some(u)))
}
#[inline(never)]
pub fn poke_parked() {
    PARKED.with(|p| {
        if let Some(u) = p.get() {
            poke(u)
        }
    })
}

// u = Box::leak(Box::new(U32 { n: 0 })), park(u) first. No argument reaches the call.
pub fn must_refute_union_ref_zero_arg_call(u: &U32) -> u32 {
    if unsafe { u.n } < 100 {
        poke_parked();
        (unsafe { u.n }) + 1
    } else {
        0
    }
}

// ---- correct twins ----

// i = 0. Nothing runs between the guard and the add.
pub fn control_owned_union_no_call(i: u32) -> u32 {
    let u = U32 { n: i };
    if unsafe { u.n } < 100 { (unsafe { u.n }) + 1 } else { 0 }
}

// i = 0. The guard reads the union after the call.
pub fn control_owned_union_guard_after_call(i: u32) -> u32 {
    let u = U32 { n: i };
    poke(&u);
    if unsafe { u.n } < 100 { (unsafe { u.n }) + 1 } else { 0 }
}

// u = &U32 { n: 0 }. The guard reads the union after the call.
pub fn control_union_ref_guard_after_call(u: &U32) -> u32 {
    poke(u);
    if unsafe { u.n } < 100 { (unsafe { u.n }) + 1 } else { 0 }
}

// i = 0. The cell field is handed to the call BEFORE the guard.
pub fn control_owned_union_cell_field_borrow_guard_after_call(i: u32) -> u32 {
    let u = U32 { n: i };
    poke_cell(unsafe { &u.c });
    if unsafe { u.n } < 100 { (unsafe { u.n }) + 1 } else { 0 }
}

// i = 0. The call may set the cell, but `n / 2 + 1` cannot overflow.
pub fn control_owned_union_add_cannot_overflow(i: u32) -> u32 {
    let u = U32 { n: i };
    if unsafe { u.n } < 100 {
        poke(&u);
        (unsafe { u.n }) / 2 + 1
    } else {
        0
    }
}

// i = 0. The call is handed ANOTHER union; `u`'s address is never taken.
pub fn control_other_union_call(i: u32) -> u32 {
    let u = U32 { n: i };
    let v = U32 { n: 0 };
    if unsafe { u.n } < 100 {
        poke(&v);
        (unsafe { u.n }) + 1
    } else {
        0
    }
}

#[repr(C)]
pub union P32 {
    pub a: u32,
    pub n: u32,
}
#[inline(never)]
pub fn look(p: &P32) -> u32 {
    unsafe { p.a }
}

// i = 0. A union with no cell: its bytes are frozen behind the shared borrow.
pub fn control_owned_frozen_union_call(i: u32) -> u32 {
    let p = P32 { n: i };
    if unsafe { p.n } < 100 {
        look(&p);
        (unsafe { p.n }) + 1
    } else {
        0
    }
}

// p = &P32 { n: 0 }. The same behind `&`.
pub fn control_frozen_union_ref_call(p: &P32) -> u32 {
    if unsafe { p.n } < 100 {
        look(p);
        (unsafe { p.n }) + 1
    } else {
        0
    }
}

// i = 0. The call is handed the struct's union field; the add reads its frozen sibling `k`.
pub fn control_owned_struct_frozen_sibling(i: u32) -> u32 {
    let h = H { k: i, u: U32 { n: 0 } };
    if h.k < 100 {
        poke(&h.u);
        h.k + 1
    } else {
        0
    }
}

// ---- INTERIOR-MUT-CHANNEL-2: a shared borrow strictly below a union that holds cell bytes ----
//
// Main PROVES the add row of every `must_refute_*` below, a false proof: each panics
// natively on the input in its comment. The borrowed place lies strictly below the union
// (`&u.c`, `&a[0].c`, `&t.1.c`, `&o.inner`, `&u.s`). It is taken before or after the guard,
// handed to a call directly or inside a struct, or parked for a zero-argument call; or the
// body sets the cell itself, with no user callee. Appended after the programs above, so
// their spans keep their lines.

#[inline(never)]
pub fn poke_md(c: &ManuallyDrop<Cell<u32>>) {
    c.set(u32::MAX);
}

// i = 0. `&u.c` handed as `&ManuallyDrop<Cell<u32>>`: no `ManuallyDrop::deref` call.
pub fn must_refute_owned_union_md_field_borrow(i: u32) -> u32 {
    let u = U32 { n: i };
    if unsafe { u.n } < 100 {
        poke_md(unsafe { &u.c });
        (unsafe { u.n }) + 1
    } else {
        0
    }
}

// i = 0. The body sets the cell itself; no user function is called.
pub fn must_refute_owned_union_cell_set_in_body(i: u32) -> u32 {
    let u = U32 { n: i };
    if unsafe { u.n } < 100 {
        unsafe { u.c.set(u32::MAX) };
        (unsafe { u.n }) + 1
    } else {
        0
    }
}

// i = 0. An array of unions, the cell field of element 0 borrowed.
pub fn must_refute_union_array_cell_field_borrow(i: u32) -> u32 {
    let a = [U32 { n: i }, U32 { n: i }];
    if unsafe { a[0].n } < 100 {
        poke_cell(unsafe { &a[0].c });
        (unsafe { a[0].n }) + 1
    } else {
        0
    }
}

// i = 0. A union in a tuple, its cell field borrowed.
pub fn must_refute_union_tuple_cell_field_borrow(i: u32) -> u32 {
    let t = (1u32, U32 { n: i });
    if unsafe { t.1.n } < 100 {
        poke_cell(unsafe { &t.1.c });
        (unsafe { t.1.n }) + 1
    } else {
        0
    }
}

#[repr(C)]
pub union Outer {
    pub inner: ManuallyDrop<U32>,
    pub m: u32,
}

// i = 0. A union nested in a union: `poke(&o.inner)` is handed a field that is not itself
// a cell but holds one; the add reads `o.m`.
pub fn must_refute_nested_union_inner_borrow(i: u32) -> u32 {
    let o = Outer { m: i };
    if unsafe { o.m } < 100 {
        poke(unsafe { &o.inner });
        (unsafe { o.m }) + 1
    } else {
        0
    }
}

// i = 0. `&u.c` is taken BEFORE the guard; the call after the guard is handed it.
pub fn must_refute_owned_union_cell_borrow_before_guard(i: u32) -> u32 {
    let u = U32 { n: i };
    let c: &Cell<u32> = unsafe { &u.c };
    if unsafe { u.n } < 100 {
        poke_cell(c);
        (unsafe { u.n }) + 1
    } else {
        0
    }
}

#[inline(never)]
pub fn poke_atomic(a: &AtomicU32) {
    a.store(u32::MAX, Ordering::Relaxed)
}

// i = 0. The atomic field itself borrowed.
pub fn must_refute_owned_atomic_union_field_borrow(i: u32) -> u32 {
    let u = UA32 { n: i };
    if unsafe { u.n } < 100 {
        poke_atomic(unsafe { &u.c });
        (unsafe { u.n }) + 1
    } else {
        0
    }
}

#[inline(never)]
pub fn poke_uc(c: &UnsafeCell<u32>) {
    unsafe { *c.get() = u32::MAX }
}

// i = 0. The `UnsafeCell` field itself borrowed.
pub fn must_refute_owned_unsafecell_union_field_borrow(i: u32) -> u32 {
    let u = UU32 { n: i };
    if unsafe { u.n } < 100 {
        poke_uc(unsafe { &u.c });
        (unsafe { u.n }) + 1
    } else {
        0
    }
}

#[inline(never)]
pub fn poke_mu(m: &MaybeUninit<Cell<u32>>) {
    unsafe { m.assume_init_ref().set(u32::MAX) }
}

// i = 0. The `MaybeUninit<Cell<u32>>` field itself borrowed.
pub fn must_refute_owned_maybe_uninit_union_field_borrow(i: u32) -> u32 {
    let u = UM32 { n: i };
    if unsafe { u.n } < 100 {
        poke_mu(unsafe { &u.c });
        (unsafe { u.n }) + 1
    } else {
        0
    }
}

#[repr(C)]
pub struct SC {
    pub c: Cell<u32>,
}
#[repr(C)]
pub union US {
    pub s: ManuallyDrop<SC>,
    pub n: u32,
}
#[inline(never)]
pub fn poke_sc(s: &SC) {
    s.c.set(u32::MAX)
}

// i = 0. The union field is a struct wrapping the cell: `poke_sc(&u.s)`.
pub fn must_refute_owned_union_struct_wrapped_cell_borrow(i: u32) -> u32 {
    let u = US { n: i };
    if unsafe { u.n } < 100 {
        poke_sc(unsafe { &u.s });
        (unsafe { u.n }) + 1
    } else {
        0
    }
}

thread_local! {
    static PARKED_CELL: Cell<*const Cell<u32>> = const { Cell::new(std::ptr::null()) };
}
#[inline(never)]
pub fn park_cell(c: &Cell<u32>) {
    PARKED_CELL.with(|p| p.set(c as *const Cell<u32>))
}
#[inline(never)]
pub fn poke_parked_cell() {
    PARKED_CELL.with(|p| {
        let c = p.replace(std::ptr::null());
        if !c.is_null() {
            unsafe { (*c).set(u32::MAX) }
        }
    })
}

// i = 0. `park_cell(&u.c)` runs before the guard; the ZERO-ARGUMENT call after it sets the
// cell through the parked pointer.
pub fn must_refute_owned_union_parked_cell_zero_arg_call(i: u32) -> u32 {
    let u = U32 { n: i };
    park_cell(unsafe { &u.c });
    if unsafe { u.n } < 100 {
        poke_parked_cell();
        (unsafe { u.n }) + 1
    } else {
        0
    }
}

pub struct CellRef<'a> {
    pub c: &'a Cell<u32>,
}
#[inline(never)]
pub fn poke_cell_ref(r: &CellRef) {
    r.c.set(u32::MAX)
}

// i = 0. `&u.c` is stored in a struct; the call is handed the struct.
pub fn must_refute_owned_union_cell_ref_in_struct(i: u32) -> u32 {
    let u = U32 { n: i };
    let r = CellRef { c: unsafe { &u.c } };
    if unsafe { u.n } < 100 {
        poke_cell_ref(&r);
        (unsafe { u.n }) + 1
    } else {
        0
    }
}

// ---- correct twins of those shapes: a fix of INTERIOR-MUT-CHANNEL-2 must keep proving them ----

// i = 0. The body sets the cell BEFORE the guard.
pub fn control_owned_union_cell_set_in_body_guard_after(i: u32) -> u32 {
    let u = U32 { n: i };
    unsafe { u.c.set(u32::MAX) };
    if unsafe { u.n } < 100 { (unsafe { u.n }) + 1 } else { 0 }
}

// i = 0. The parked cell is poked BEFORE the guard.
pub fn control_owned_union_parked_cell_poked_before_guard(i: u32) -> u32 {
    let u = U32 { n: i };
    park_cell(unsafe { &u.c });
    poke_parked_cell();
    if unsafe { u.n } < 100 { (unsafe { u.n }) + 1 } else { 0 }
}

// i = 0. The nested union, the call BEFORE the guard.
pub fn control_nested_union_guard_after_call(i: u32) -> u32 {
    let o = Outer { m: i };
    poke(unsafe { &o.inner });
    if unsafe { o.m } < 100 { (unsafe { o.m }) + 1 } else { 0 }
}

// i = 0. The cell field is borrowed, but `u.n / 2 + 1` cannot overflow.
pub fn control_owned_union_cell_field_borrow_cannot_overflow(i: u32) -> u32 {
    let u = U32 { n: i };
    if unsafe { u.n } < 100 {
        poke_cell(unsafe { &u.c });
        (unsafe { u.n }) / 2 + 1
    } else {
        0
    }
}

// i = 0. Two unions: the cell field of `v` is borrowed, the add reads `u.n`.
pub fn control_other_union_cell_field_borrow(i: u32) -> u32 {
    let u = U32 { n: i };
    let v = U32 { n: 0 };
    if unsafe { u.n } < 100 {
        poke_cell(unsafe { &v.c });
        (unsafe { u.n }) + 1
    } else {
        0
    }
}

// i = 0. A tuple: the union's cell field is borrowed, the add reads the frozen sibling `t.0`.
pub fn control_union_tuple_frozen_sibling(i: u32) -> u32 {
    let t = (i, U32 { n: 0 });
    if t.0 < 100 {
        poke_cell(unsafe { &t.1.c });
        t.0 + 1
    } else {
        0
    }
}

// i = 0. A struct: `h.u.c` is borrowed, the add reads the frozen sibling `h.k`.
pub fn control_owned_struct_cell_field_borrow_frozen_sibling(i: u32) -> u32 {
    let h = H { k: i, u: U32 { n: 0 } };
    if h.k < 100 {
        poke_cell(unsafe { &h.u.c });
        h.k + 1
    } else {
        0
    }
}
