extern crate fake;
#[inline(never)]
pub fn boom(v: &fake::vec::Vec<u8>) -> Vec<u64> {
    v.into_iter().collect()
}
