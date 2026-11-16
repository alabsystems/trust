// Trust: KNOWN_HAZARDS BACKING-FIRST-LOAD-1. A certified `#[trust::backing]` struct's
// use-site ASSUME `alloc_size >= len` bounded a pointer by whichever local FIRST loaded
// `len`, keyed on the base LOCAL, so a length read from one value bounded a pointer
// read from another (`cross`, `two`), a reassigned length local stood for the field
// (`add_bad`, `slice_bad`), and a pointer joined from two values kept the walk's
// last-writer tag (`join`). Every `bad` body below is UB for some input; its
// `[unsafe:sep:offset]` / `from_raw_parts` row must not be PROVED. `get` is the control:
// its row must still prove. The probes are the 2026-09-30 review's `backing_stale3.rs` /
// `backing_stale4.rs`, in the `.add` call spelling (the intrinsic `offset` spelling is
// `Rvalue::PtrOffset`, refused on main with its own `UnsupportedMir` row). On main
// `5a5545798b`'s stage 1, `add_bad`, `cross` and `join` PROVED. A `from_raw_parts` copy
// bound has no backend in this posture (`unknown`), so its rows are pinned only against
// `proved`; the crate test `sep_engine_backing_first_load_tests` judges them. The RAW
// annotations at the end REQUIRE `get`'s row proved and the `.add` rows of `add_bad`, `cross`,
// `join` and `two` present and failed, so a row that vanishes or moves fails this test
// instead of passing every `forbid-output` with nothing to check.
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ compile-flags: -Ztrust-verify-output=json --error-format=human
//@ build-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//@ forbid-output: "line_start":56,"col_start":35,"line_end":56,"col_end":50},"outcome":"failed"
//@ forbid-output: "line_start":56,"col_start":35,"line_end":56,"col_end":50},"outcome":"unknown"
//@ forbid-output: "line_start":63,"col_start":28,"line_end":63,"col_end":43},"outcome":"proved"
//@ forbid-output: "line_start":70,"col_start":29,"line_end":70,"col_end":69},"outcome":"proved"
//@ forbid-output: "line_start":79,"col_start":28,"line_end":79,"col_end":40},"outcome":"proved"
//@ forbid-output: "line_start":85,"col_start":35,"line_end":85,"col_end":43},"outcome":"proved"
//@ forbid-output: "line_start":94,"col_start":24,"line_end":94,"col_end":36},"outcome":"proved"
#![feature(register_tool)]
#![register_tool(trust)]
#![allow(dead_code, unused_mut, unused_variables, unused_assignments)]

extern "C" {
    fn mmap(addr: *mut u8, len: usize, prot: i32, flags: i32, fd: i32, offset: i64) -> *mut u8;
}

#[trust::backing]
pub struct Buf {
    ptr: *const u8,
    len: usize,
}

impl Buf {
    // Sole establishing constructor: the mapping is exactly `len` bytes.
    pub unsafe fn map(len: usize) -> Buf {
        let p = mmap(core::ptr::null_mut(), len, 0, 0, -1, 0);
        Buf { ptr: p as *const u8, len }
    }

    // CONTROL: in bounds whenever `i < self.len`.
    pub fn get(&self, i: usize) -> *const u8 {
        if i < self.len { unsafe { self.ptr.add(i) } } else { self.ptr }
    }

    // `Buf::map(10).add_bad(1 << 39)` offsets 2^39 bytes into a 10-byte mapping.
    pub fn add_bad(&self, i: usize) -> *const u8 {
        let mut n = self.len;
        n = 1 << 40;
        if i < n { unsafe { self.ptr.add(i) } } else { self.ptr }
    }

    // `Buf::map(10).slice_bad(1 << 39)` reads 2^39 bytes of a 10-byte mapping.
    pub fn slice_bad(&self, i: usize) -> &[u8] {
        let mut n = self.len;
        n = 1 << 40;
        if i <= n { unsafe { core::slice::from_raw_parts(self.ptr, i) } } else { &[] }
    }

    // `Buf::map(1 << 40).cross(&Buf::map(2), 1 << 39)`: the bound is `self`'s, the
    // pointer `other`'s.
    pub fn cross(&self, other: &Buf, i: usize) -> *const u8 {
        let mut s = self;
        let n = s.len;
        s = other;
        if i < n { unsafe { s.ptr.add(i) } } else { s.ptr }
    }

    // `Buf::map(1 << 40).join(&Buf::map(2), true, 1 << 39)`.
    pub fn join(&self, other: &Buf, c: bool, i: usize) -> *const u8 {
        let q = if c { other.ptr } else { self.ptr };
        if i < self.len { unsafe { q.add(i) } } else { q }
    }
}

// `two(&Buf::map(1 << 40), &Buf::map(2), 1 << 39)`.
pub fn two(a: &Buf, b: &Buf, i: usize) -> *const u8 {
    let mut s = a;
    let n = s.len;
    s = b;
    if i < n { unsafe { s.ptr.add(i) } } else { s.ptr }
}

//~? RAW "line_start":56,"col_start":35,"line_end":56,"col_end":50},"outcome":"proved"
//~? RAW "line_start":63,"col_start":28,"line_end":63,"col_end":43},"outcome":"failed"
//~? RAW "line_start":79,"col_start":28,"line_end":79,"col_end":40},"outcome":"failed"
//~? RAW "line_start":85,"col_start":35,"line_end":85,"col_end":43},"outcome":"failed"
//~? RAW "line_start":94,"col_start":24,"line_end":94,"col_end":36},"outcome":"failed"
