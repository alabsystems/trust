#![allow(dead_code)]

pub async fn unused() -> u32 {
    7
}

pub struct Droppable(u8);
impl Drop for Droppable {
    fn drop(&mut self) {
        std::hint::black_box(self.0);
    }
}

#[inline(always)]
pub fn inlined(value: u8) -> u8 {
    value
}
