#![no_std]
extern crate alloc;
extern crate std;
#[inline(never)]
pub fn boom(v: &std::vec::Vec<u8>) -> alloc::vec::Vec<u64> {
    v.into_iter().collect()
}
