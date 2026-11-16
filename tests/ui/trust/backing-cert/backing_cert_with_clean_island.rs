//@ revisions: certifies writer
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory
//@ compile-flags: -Ztrust-verify-output=json --error-format=human
//@ build-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//@ rustc-env:TRUST_CERT_DEBUG=1
//@ forbid-output: backing inventory INCOMPLETE
//@ forbid-output: panicked
//@[certifies] forbid-output: DENIED
//@[certifies] forbid-output: "line_start":63,"col_start":36,"line_end":63,"col_end":51},"outcome":"failed"
//@[writer] forbid-output: "line_start":63,"col_start":36,"line_end":63,"col_end":51},"outcome":"proved"
//! A crate that pairs a `clean { … }` island with a `#[trust::backing]` struct.
//!
//! The island takes `DefKind::GlobalAsm` (`def_collector.rs`: `DefKind` has no island
//! variant), and the escape census's free-item walk asked every `DefKind::GlobalAsm`
//! item for its assembly operands with `expect_global_asm` — an ICE
//! (`expect_global_asm: found Item{.. kind: CleanIsland ..}`) under
//! `-Ztrust-verify=on` in every such crate, on `origin/main` `93f05556da` and after it.
//! The census now tells the two apart by the HIR item kind: an island names no
//! operand, and the functions it declares are Clean-origin bodies in `mir_keys`,
//! which the inventory scans like any other body.
//!
//! `certifies`: the island and `Buf` coexist; `Buf` certifies and `get`'s
//! `[unsafe:sep:offset]` row (line 63) is not `failed`. `writer`: a body writes
//! `Buf`'s length through a raw pointer; the census still runs with the island
//! present and denies `Buf`, so the row is not `proved`.

#![feature(register_tool)]
#![register_tool(trust)]
#![allow(dead_code)]

extern "C" {
    fn mmap(addr: *mut u8, len: usize, prot: i32, flags: i32, fd: i32, offset: i64) -> *mut u8;
}

const fn inc(x: u64) -> u64 {
    x.wrapping_add(1)
}

clean {
    def twice_inc (x : UInt64) : UInt64 := inc (inc x)
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

    pub fn get(&self, i: usize) -> u8 {
        if i < self.len { unsafe { *self.ptr.add(i) } } else { 0 }
    }
}

pub fn use_island() -> u64 {
    twice_inc(1)
}

#[cfg(writer)]
pub fn grow(b: &mut Buf) {
    let p = &raw mut b.len;
    unsafe { *p = 1 << 20 }
}

fn main() {}
