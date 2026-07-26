// A faithful standalone copy of aterm's REAL `aterm-scrollback/src/mmap.rs`
// shape: `*mut u8` backing pointer, `ptr.cast::<u8>()`, MAP_SHARED, and a
// fallible `Result`/`Option`-wrapped constructor — exercising the certification
// on the actual code pattern (not just the minimal fixture). The `libc` shim
// stands in for the crate dependency so this compiles standalone.
//
//   trustc -Z trust-verify-output=json --crate-type lib aterm_mmap_faithful.rs
//
// Expected: certified (sealed `#[trust::backing]` + the mmap constructor
// establishes `alloc_size == len`) ⇒ as_slice/slice backing obligations PROVE.
#![cfg_attr(trust_verify, feature(register_tool))]
#![cfg_attr(trust_verify, register_tool(trust))]
#![allow(dead_code)]

mod libc {
    use std::ffi::c_void;
    pub const PROT_READ: i32 = 1;
    pub const PROT_WRITE: i32 = 2;
    pub const MAP_SHARED: i32 = 1;
    pub const MAP_FAILED: *mut c_void = usize::MAX as *mut c_void;
    extern "C" {
        pub fn mmap(
            addr: *mut c_void,
            len: usize,
            prot: i32,
            flags: i32,
            fd: i32,
            offset: i64,
        ) -> *mut c_void;
    }
}

#[cfg_attr(trust_verify, trust::backing)]
pub struct MmapMut {
    ptr: *mut u8,
    len: usize,
}

impl MmapMut {
    /// Mirror of aterm's `map_mut`: maps `len` bytes and stores the SAME `len`,
    /// so the construction establishes `alloc_size(ptr) == len`.
    #[cfg_attr(trust_verify, trust::single_writer)]
    pub unsafe fn map_mut(fd: i32, len: usize) -> Option<Self> {
        let ptr = libc::mmap(
            std::ptr::null_mut(),
            len,
            libc::PROT_READ | libc::PROT_WRITE,
            libc::MAP_SHARED,
            fd,
            0,
        );
        if ptr == libc::MAP_FAILED {
            return None;
        }
        Some(Self { ptr: ptr.cast::<u8>(), len })
    }

    pub fn as_slice(&self) -> &[u8] {
        // SAFETY: ptr is a valid mmap of len bytes; slice length IS self.len.
        unsafe { std::slice::from_raw_parts(self.ptr, self.len) }
    }

    pub fn slice(&self, start: usize, len: usize) -> Option<&[u8]> {
        let end = start.checked_add(len)?;
        if end > self.len {
            return None;
        }
        // SAFETY: start + len <= self.len, so the sub-range stays within the map.
        Some(unsafe { std::slice::from_raw_parts(self.ptr.add(start), len) })
    }
}
