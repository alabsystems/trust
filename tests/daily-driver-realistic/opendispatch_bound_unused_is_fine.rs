pub trait Shape {
    fn area(&self) -> u64;
}
pub fn f<T: Shape>(_s: &T, x: u32) -> u32 {
    x
}
