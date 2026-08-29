extern crate mycrate;
#[inline(never)]
pub fn boom(v: &mycrate::vec::Vec<u8>) -> Vec<u64> {
    v.into_iter().collect()
}
