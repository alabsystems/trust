pub trait Shape {
    fn area(&self) -> u64;
}
pub struct R {
    pub w: u32,
}
impl Shape for R {
    fn area(&self) -> u64 {
        self.w as u64
    }
}
pub fn f<T: Shape>(s: &T) -> u64 {
    s.area()
}
