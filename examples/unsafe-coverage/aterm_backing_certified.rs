// End-to-end validation of interprocedural backing certification.
//
// `MmapMut { ptr, len }` has PRIVATE backing fields and `#[trust::backing]`, a
// constructor `map` that ESTABLISHES the invariant (the pointer is an `mmap` of
// exactly `len` bytes), and two USE sites. With the analysis-phase certificate
// (sealed ∩ established), the use-site obligations must DISCHARGE (proved) — the
// sound restoration of what the unsound `len > len` discharge used to fake.
//
// Compile:
//   trustc -Z trust-verify-output=both --crate-type lib aterm_backing_certified.rs
// Controls that must fall back to CAUGHT:
//   - drop `#[trust::backing]`            (not sealed/opted-in)
//   - make a backing field `pub`          (not sealed ⇒ external construction possible)
//   - construct `MmapMut { ptr: p, len: len + 1 }` (establish `len < len+1` is SAT)
#![cfg_attr(trust_verify, feature(register_tool))]
#![cfg_attr(trust_verify, register_tool(trust))]
#![allow(dead_code)]

use std::slice;

extern "C" {
    // The real 6-arg mmap(addr, len, prot, flags, fd, offset): returns a region
    // of exactly `len` bytes, so the constructor's establish obligation is
    // `len < len` (UNSAT) — the invariant holds at construction.
    fn mmap(addr: *mut u8, len: usize, prot: i32, flags: i32, fd: i32, offset: i64) -> *mut u8;
}

#[cfg_attr(trust_verify, trust::backing)]
pub struct MmapMut {
    ptr: *const u8,
    len: usize,
}

impl MmapMut {
    // Constructor: ESTABLISHES `alloc_size(ptr) >= len` (here `== len`).
    pub unsafe fn map(len: usize) -> MmapMut {
        let p = mmap(core::ptr::null_mut(), len, 0, 0, -1, 0);
        MmapMut { ptr: p as *const u8, len }
    }

    // USE site 1: `from_raw_parts(self.ptr, self.len)` — discharges via the
    // certificate (`alloc_size >= self.len`), since the slice length IS self.len.
    pub fn as_slice(&self) -> &[u8] {
        unsafe { slice::from_raw_parts(self.ptr, self.len) }
    }

    // USE site 2: guarded offset slice — `start + len <= self.len` plus the
    // certificate discharge both the `.add` offset and the from_raw_parts bounds.
    pub fn slice(&self, start: usize, len: usize) -> Option<&[u8]> {
        let end = start.checked_add(len)?;
        if end > self.len {
            return None;
        }
        Some(unsafe { slice::from_raw_parts(self.ptr.add(start), len) })
    }
}
