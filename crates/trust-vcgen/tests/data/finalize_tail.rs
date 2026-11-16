//! TRUST-KI-1015-1, the padding-tail shape of aterm-digest `Sha256::finalize`
//! (sha256.rs:141-155 at aterm 848d791bd):
//!
//! ```text
//! self.buf[self.buf_len] = 0x80;
//! self.buf_len += 1;
//! if self.buf_len > BLOCK_LEN - 8 { self.buf[self.buf_len..].fill(0); ..; self.buf_len = 0; }
//! self.buf[self.buf_len..BLOCK_LEN - 8].fill(0);       // the row: in range on every path
//! ```
//!
//! `ok_*` are CORRECT for every input (no execution panics); `bad_*` are WRONG twins,
//! each with an input that panics at the tail slice (tests/native.rs runs them).

pub const BLOCK_LEN: usize = 64;

pub struct Pad {
    pub state: [u32; 8],
    pub buf: [u8; BLOCK_LEN],
    pub buf_len: usize,
    pub len: u64,
}

fn compress(state: &mut [u32; 8], block: &[u8; BLOCK_LEN]) {
    state[0] = state[0].wrapping_add(block[0] as u32);
}

impl Pad {
    /// aterm's shape verbatim (by-value `self`), plus an entry guard so the `0x80`
    /// write is total (aterm relies on a private-field invariant there instead).
    pub fn ok_finalize(mut self) -> [u8; BLOCK_LEN] {
        if self.buf_len >= BLOCK_LEN {
            return self.buf;
        }
        let bit_len = self.len.wrapping_mul(8);
        self.buf[self.buf_len] = 0x80;
        self.buf_len += 1;
        if self.buf_len > BLOCK_LEN - 8 {
            self.buf[self.buf_len..].fill(0);
            let block = self.buf;
            compress(&mut self.state, &block);
            self.buf_len = 0;
        }
        self.buf[self.buf_len..BLOCK_LEN - 8].fill(0);
        self.buf[BLOCK_LEN - 8..].copy_from_slice(&bit_len.to_be_bytes());
        self.buf
    }

    /// The same through `&mut self` (the field is `(*self).buf_len`).
    pub fn ok_finalize_ref(&mut self) {
        if self.buf_len >= BLOCK_LEN {
            return;
        }
        self.buf[self.buf_len] = 0x80;
        self.buf_len += 1;
        if self.buf_len > BLOCK_LEN - 8 {
            self.buf[self.buf_len..].fill(0);
            self.buf_len = 0;
        }
        self.buf[self.buf_len..BLOCK_LEN - 8].fill(0);
    }

    /// WRONG: the threshold is one too high; `buf_len == 56` on entry reaches
    /// `buf[57..56]`.
    pub fn bad_threshold(mut self) -> [u8; BLOCK_LEN] {
        if self.buf_len >= BLOCK_LEN {
            return self.buf;
        }
        self.buf[self.buf_len] = 0x80;
        self.buf_len += 1;
        if self.buf_len > BLOCK_LEN - 7 {
            self.buf[self.buf_len..].fill(0);
            self.buf_len = 0;
        }
        self.buf[self.buf_len..BLOCK_LEN - 8].fill(0);
        self.buf
    }

    /// WRONG: the spill branch forgets to reset `buf_len`.
    pub fn bad_no_reset(mut self) -> [u8; BLOCK_LEN] {
        if self.buf_len >= BLOCK_LEN {
            return self.buf;
        }
        self.buf[self.buf_len] = 0x80;
        self.buf_len += 1;
        if self.buf_len > BLOCK_LEN - 8 {
            self.buf[self.buf_len..].fill(0);
        }
        self.buf[self.buf_len..BLOCK_LEN - 8].fill(0);
        self.buf
    }

    /// WRONG: the guard tests the length from BEFORE the increment.
    pub fn bad_stale_guard(mut self) -> [u8; BLOCK_LEN] {
        if self.buf_len >= BLOCK_LEN {
            return self.buf;
        }
        let before = self.buf_len;
        self.buf[self.buf_len] = 0x80;
        self.buf_len += 1;
        if before > BLOCK_LEN - 8 {
            self.buf[self.buf_len..].fill(0);
            self.buf_len = 0;
        }
        self.buf[self.buf_len..BLOCK_LEN - 8].fill(0);
        self.buf
    }

    /// WRONG: the increment happens after the guard.
    pub fn bad_increment_after_guard(mut self) -> [u8; BLOCK_LEN] {
        if self.buf_len >= BLOCK_LEN {
            return self.buf;
        }
        self.buf[self.buf_len] = 0x80;
        if self.buf_len > BLOCK_LEN - 8 {
            self.buf[self.buf_len..].fill(0);
            self.buf_len = 0;
        }
        self.buf_len += 1;
        self.buf[self.buf_len..BLOCK_LEN - 8].fill(0);
        self.buf
    }

    /// WRONG: a second write of `buf_len` between the guard and the slice.
    pub fn bad_write_after_guard(mut self) -> [u8; BLOCK_LEN] {
        if self.buf_len >= BLOCK_LEN {
            return self.buf;
        }
        self.buf[self.buf_len] = 0x80;
        self.buf_len += 1;
        if self.buf_len > BLOCK_LEN - 8 {
            self.buf[self.buf_len..].fill(0);
            self.buf_len = 0;
        }
        self.buf_len += 1;
        self.buf[self.buf_len..BLOCK_LEN - 8].fill(0);
        self.buf
    }

    /// WRONG, through `&mut self`: the threshold is one too high.
    pub fn bad_threshold_ref(&mut self) {
        if self.buf_len >= BLOCK_LEN {
            return;
        }
        self.buf[self.buf_len] = 0x80;
        self.buf_len += 1;
        if self.buf_len > BLOCK_LEN - 7 {
            self.buf[self.buf_len..].fill(0);
            self.buf_len = 0;
        }
        self.buf[self.buf_len..BLOCK_LEN - 8].fill(0);
    }

    /// WRONG: the guard tests a copy taken BETWEEN two increments, so it bounds the
    /// first incremented value and not the second.
    pub fn bad_guard_on_stale_copy(mut self) -> [u8; BLOCK_LEN] {
        if self.buf_len >= BLOCK_LEN - 1 {
            return self.buf;
        }
        self.buf_len += 1;
        let copied = self.buf_len;
        self.buf_len += 1;
        if copied > BLOCK_LEN - 8 {
            self.buf[self.buf_len..].fill(0);
            self.buf_len = 0;
        }
        self.buf[self.buf_len..BLOCK_LEN - 8].fill(0);
        self.buf
    }
}

/// The tail with the guard on the ENTRY length (no increment before it): correct.
pub fn ok_entry_tail(mut pad: Pad) -> [u8; BLOCK_LEN] {
    if pad.buf_len > BLOCK_LEN - 8 {
        pad.buf_len = 0;
    }
    pad.buf[pad.buf_len..BLOCK_LEN - 8].fill(0);
    pad.buf
}

/// The same tail over plain locals (no struct field): a control.
pub fn ok_local(mut buf: [u8; BLOCK_LEN], buf_len: usize) -> [u8; BLOCK_LEN] {
    if buf_len >= BLOCK_LEN {
        return buf;
    }
    let mut n = buf_len;
    buf[n] = 0x80;
    n += 1;
    if n > BLOCK_LEN - 8 {
        buf[n..].fill(0);
        n = 0;
    }
    buf[n..BLOCK_LEN - 8].fill(0);
    buf
}

/// WRONG, the guard on the ENTRY length: the threshold is one too high; `buf_len == 57`
/// on entry takes the skip edge to `buf[57..56]`.
pub fn bad_entry_threshold(mut pad: Pad) -> [u8; BLOCK_LEN] {
    if pad.buf_len > BLOCK_LEN - 7 {
        pad.buf_len = 0;
    }
    pad.buf[pad.buf_len..BLOCK_LEN - 8].fill(0);
    pad.buf
}

/// WRONG, the guard on the ENTRY length: the clamp stores `57`, not `0`, so every
/// `buf_len > 56` reaches `buf[57..56]` through the guarded arm.
pub fn bad_entry_clamp_value(mut pad: Pad) -> [u8; BLOCK_LEN] {
    if pad.buf_len > BLOCK_LEN - 8 {
        pad.buf_len = BLOCK_LEN - 7;
    }
    pad.buf[pad.buf_len..BLOCK_LEN - 8].fill(0);
    pad.buf
}

/// WRONG, the guard on the ENTRY length: the guard is inverted, so the skip edge carries
/// every `buf_len > 56` to the slice.
pub fn bad_entry_inverted(mut pad: Pad) -> [u8; BLOCK_LEN] {
    if pad.buf_len <= BLOCK_LEN - 8 {
        pad.buf_len = 0;
    }
    pad.buf[pad.buf_len..BLOCK_LEN - 8].fill(0);
    pad.buf
}

/// WRONG, a store through a `&mut` borrow of the length between the guard's read and the
/// guard: the guard tests the length from before the store, which sets it to `57`. Every
/// `buf_len <= 56` takes the skip edge to `buf[57..56]`.
pub fn bad_entry_ref_store(mut pad: Pad) -> [u8; BLOCK_LEN] {
    let len = &mut pad.buf_len;
    let tested = *len;
    *len = BLOCK_LEN - 7;
    if tested > BLOCK_LEN - 8 {
        pad.buf_len = 0;
    }
    pad.buf[pad.buf_len..BLOCK_LEN - 8].fill(0);
    pad.buf
}

/// WRONG, the same through a raw pointer to a local length.
pub fn bad_local_raw_store(mut buf: [u8; BLOCK_LEN], buf_len: usize) -> [u8; BLOCK_LEN] {
    let mut n = buf_len;
    let p: *mut usize = &raw mut n;
    let tested = n;
    unsafe { *p = BLOCK_LEN - 7 };
    if tested > BLOCK_LEN - 8 {
        n = 0;
    }
    buf[n..BLOCK_LEN - 8].fill(0);
    buf
}

/// WRONG, the clamp's arm stores `0` and then `57` through a raw pointer taken after the
/// first store: every `buf_len > 56` reaches `buf[57..56]` through the arm.
pub fn bad_local_arm_raw_store(mut buf: [u8; BLOCK_LEN], buf_len: usize) -> [u8; BLOCK_LEN] {
    let mut n = buf_len;
    if n > BLOCK_LEN - 8 {
        n = 0;
        let p: *mut usize = &raw mut n;
        unsafe { *p = BLOCK_LEN - 7 };
    }
    buf[n..BLOCK_LEN - 8].fill(0);
    buf
}

/// WRONG, the same store with an `else` arm (both arms define the length).
pub fn bad_local_two_arm_raw_store(mut buf: [u8; BLOCK_LEN], buf_len: usize) -> [u8; BLOCK_LEN] {
    let mut n = buf_len;
    if n > BLOCK_LEN - 8 {
        n = 0;
        let p: *mut usize = &raw mut n;
        unsafe { *p = BLOCK_LEN - 7 };
    } else {
        n = 1;
    }
    buf[n..BLOCK_LEN - 8].fill(0);
    buf
}

/// WRONG, two raw pointers that may be equal: the guard tests `*q` from before a store
/// through `p`. Called with `p == q`, every `*q <= 56` takes the skip edge to
/// `buf[57..56]`.
///
/// # Safety
///
/// `p` and `q` are valid for reads and writes.
pub unsafe fn bad_raw_alias_store(p: *mut usize, q: *mut usize, buf: &mut [u8; BLOCK_LEN]) {
    let tested = unsafe { *q };
    unsafe { *p = BLOCK_LEN - 7 };
    if tested > BLOCK_LEN - 8 {
        unsafe { *q = 0 };
    }
    let n = unsafe { *q };
    buf[n..BLOCK_LEN - 8].fill(0);
}

/// WRONG, the same store with no join: the slice sits on the guard's own false edge.
///
/// # Safety
///
/// `p` and `q` are valid for reads and writes.
pub unsafe fn bad_raw_alias_store_straight(
    p: *mut usize,
    q: *mut usize,
    buf: &mut [u8; BLOCK_LEN],
) {
    let tested = unsafe { *q };
    unsafe { *p = BLOCK_LEN - 7 };
    if tested <= BLOCK_LEN - 8 {
        let n = unsafe { *q };
        buf[n..BLOCK_LEN - 8].fill(0);
    }
}

// Decided twins (the adversarial review of SKIP-EDGE-JOIN-1, 2026-10-15). The rows above
// that store through a pointer are not decided on main (the bound resolution declines a
// slice over an address-taken length), so they cannot show whether a restated fact ignores
// a store. These return `56 - n`, an arithmetic row the in-process `ay` decides; each
// panics natively there ("attempt to subtract with overflow"). The literal `56` keeps the
// comparison in the switch block.

/// WRONG, the store the guard does not see is a DECLINED definition in the switch block. The
/// guard tests `t`, a copy of `n` made in an earlier block (`k + 1`'s overflow check ends it),
/// and the switch block rewrites `n` with an unsigned non-constant `%`, which definition
/// extraction declines: only the fixpoint's kill of a declined destination drops `t == n`
/// there. `len = 0, a = 57, d = 100` reaches `56 - 57`.
pub fn bad_declined_rem_in_switch(len: usize, a: usize, d: usize) -> usize {
    let mut n = len;
    let t = n;
    let m = d + 1;
    n = a % m;
    if t > 56 {
        n = 0;
    }
    56 - n
}

/// WRONG, the same with a store of `57` into a byte of `n` through a `*mut u8`, in the switch
/// block: only the fixpoint's deref-store havoc drops `t == n` there. `len = 0` reaches
/// `56 - 57` (little-endian; on a big-endian target `n` becomes `57 << 56`, which panics
/// too).
pub fn bad_byte_store_in_switch(len: usize, k: usize) -> usize {
    let mut n = len;
    let t = n;
    let m = k + 1;
    let p = (&raw mut n) as *mut u8;
    unsafe { *p = 57 };
    if t > 56 {
        n = 0;
    }
    56 - n + m * 0
}

/// WRONG, the decided twin of `bad_entry_ref_store`: a store through a `&mut` borrow of the
/// length between the guard's read and the guard. `len <= 56` reaches `56 - 57`.
pub fn bad_entry_ref_store_sub(mut len: usize) -> usize {
    let r = &mut len;
    let tested = *r;
    *r = 57;
    if tested > 56 {
        len = 0;
    }
    56 - len
}

/// WRONG, the decided twin of `bad_local_raw_store`: a raw-pointer store between the guard's
/// read and the guard. `len <= 56` reaches `56 - 57`.
pub fn bad_local_raw_store_sub(len: usize) -> usize {
    let mut n = len;
    let p: *mut usize = &raw mut n;
    let tested = n;
    unsafe { *p = 57 };
    if tested > 56 {
        n = 0;
    }
    56 - n
}

/// WRONG, the decided twin of `bad_local_arm_raw_store`: the arm stores `0`, then `57` through
/// a raw pointer. `len > 56` reaches `56 - 57`.
pub fn bad_local_arm_raw_store_sub(len: usize) -> usize {
    let mut n = len;
    if n > 56 {
        n = 0;
        let p: *mut usize = &raw mut n;
        unsafe { *p = 57 };
    }
    56 - n
}

/// WRONG, the decided twin of `bad_local_two_arm_raw_store` (both arms define the length).
pub fn bad_local_two_arm_raw_store_sub(len: usize) -> usize {
    let mut n = len;
    if n > 56 {
        n = 0;
        let p: *mut usize = &raw mut n;
        unsafe { *p = 57 };
    } else {
        n = 1;
    }
    56 - n
}

/// WRONG, the arm's store for a PARAMETER, which no merge defines (the fix's arm half answers
/// for it): the arm stores `0`, then `57` through a `&mut`. `n > 56` reaches `56 - 57`.
pub fn bad_param_arm_ref_store_sub(mut n: usize) -> usize {
    if n > 56 {
        n = 0;
        let r = &mut n;
        *r = 57;
    }
    56 - n
}

/// A `static mut` length (the review's `adv3_static`).
pub static mut GLEN: usize = 0;

/// Sets [`GLEN`] to `57`.
#[inline(never)]
pub fn poke_global() {
    unsafe { GLEN = BLOCK_LEN - 7 }
}

/// WRONG, the arm resets a `static mut` length and a callee then sets it to `57`: every
/// `GLEN > 56` on entry reaches `56 - 57`. The subtraction's row stays FAILED. Its read of the
/// static carries an `[unsafe:sep:deref] null check` row, which is CORRECT (a static's address
/// is never null) but which the separation lane does not model: the goal names a fresh
/// pointer symbol no fact mentions, so only the path condition decides it, and the read on
/// the line before (`GLEN = 0`) is already FAILED on main for that reason.
#[allow(unused_variables, unused_assignments)]
pub fn bad_static_arm_call(mut side: usize) -> usize {
    if unsafe { GLEN } > BLOCK_LEN - 8 {
        unsafe { GLEN = 0 };
        poke_global();
        side = 1;
    }
    (BLOCK_LEN - 8) - unsafe { GLEN }
}
