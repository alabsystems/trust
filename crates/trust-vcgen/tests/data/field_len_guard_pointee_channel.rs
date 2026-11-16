// Counter-programs for the field-length guard fact (`container_len`'s
// `build_len_guard_field_map`) and the place-stability rule it asks
// (`place_is_body_stable`). The fact is `coll_len(&self.v) >= C` after a dominating
// `if self.v.len() < C { return }`; it is sound only while the `Vec` at `self.v`
// cannot change between the guard and the index. `self.v` lives BEHIND `self`'s
// `Deref`, and a pointer to it minted by `&raw const *self` (then cast to `*mut`)
// writes it: that write is defined under Tree Borrows when `self` is `&mut`. Until
// 2026-09-30 the fact asked only whether `self`'s own SLOT was stable, which leaves
// `&raw const (*self)` off by design, and `self.v[3]` was kernel-certified PROVED on
// the compiler's entry (the r8c union review's F1).
//
// Every `*_raw_const*` body and `box_root_raw_const` panic natively (`index out of
// bounds: the len is 0 but the index is 3`, -O0 and -O3). `field_len_guard_raw_mut`
// is the same program through `&raw mut *self`, which the slot rule always counted
// (the control that refuted before the fix). `field_len_guard_no_channel` and
// `field_len_guard_shared` are PRECISION controls the fact exists for: nothing can
// write the field, and the index must still prove.
//
// Fixtures: tests/fixtures/field_len_guard_pointee_channel_<fn>_mir.json (a method
// `VH::f` is saved as `f`), dumped from this file by Trust `main` stage 1 a7ea88986d
// with
//   rustc --edition 2024 --crate-type lib -Ztrust-verify-profile=unix_hardened \
//         -Ztrust-policy=advisory -Ztrust-dump=mir:<dir> \
//         crates/trust-vcgen/tests/data/field_len_guard_pointee_channel.rs
// run from the repository root (so `span.file` is already repo-relative; nothing
// in the dumps was edited).
#![allow(unused_mut, dead_code)]

pub struct VH {
    pub v: Vec<u8>,
}

#[inline(never)]
pub fn clear_vh(p: *mut VH) {
    unsafe { (*p).v.clear() }
}

impl VH {
    // A callee handed `&raw const *self` (cast to `*mut`) clears the `Vec`.
    pub fn field_len_guard_raw_const(&mut self) -> u8 {
        if self.v.len() < 4 {
            return 0;
        }
        clear_vh(&raw const *self as *mut VH);
        self.v[3]
    }

    // CONTROL: the same through `&raw mut *self`.
    pub fn field_len_guard_raw_mut(&mut self) -> u8 {
        if self.v.len() < 4 {
            return 0;
        }
        clear_vh(&raw mut *self);
        self.v[3]
    }

    // The write done in the body, through the same pointer.
    pub fn field_len_guard_raw_const_direct(&mut self) -> u8 {
        if self.v.len() < 4 {
            return 0;
        }
        let p = &raw const *self as *mut VH;
        unsafe { (*p).v = Vec::new() };
        self.v[3]
    }

    // PRECISION: no pointer to `*self` is minted; the index proves from the guard.
    pub fn field_len_guard_no_channel(&mut self) -> u8 {
        if self.v.len() < 4 {
            return 0;
        }
        self.v[3]
    }

    // PRECISION: the same under `&self`.
    pub fn field_len_guard_shared(&self) -> u8 {
        if self.v.len() < 4 {
            return 0;
        }
        self.v[3]
    }
}

// A free function over `h: &mut VH`, the index symbolic and guarded.
pub fn field_len_guard_free(h: &mut VH, i: usize) -> u8 {
    if h.v.len() < 4 {
        return 0;
    }
    clear_vh(&raw const *h as *mut VH);
    if i < 4 { h.v[i] } else { 0 }
}

// A `Box` root: the guard and the index read `(*b).v`, and a callee clears it
// through `&raw const *b`.
pub fn box_root_raw_const(mut b: Box<VH>) -> u8 {
    if b.v.len() < 4 {
        return 0;
    }
    clear_vh(&raw const *b as *mut VH);
    b.v[3]
}
