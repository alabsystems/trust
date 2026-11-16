#![allow(dead_code)]

#[inline(never)]
pub fn identity<T>(value: T) -> T {
    value
}

pub struct Owner(pub u8);
impl Drop for Owner {
    #[inline(never)]
    fn drop(&mut self) {
        std::hint::black_box(self.0);
    }
}

pub static VALUE: u8 = 7;

pub fn instances() -> (u8, u16) {
    let owner = Owner(VALUE);
    let closure = move || owner;
    drop(closure());
    (identity::<u8>(VALUE), identity::<u16>(9))
}

fn main() {
    std::hint::black_box(instances());
}
