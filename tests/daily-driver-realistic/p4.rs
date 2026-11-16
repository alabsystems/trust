pub trait Shape {
    fn area(&self) -> u64;
}
pub struct Rect {
    pub w: u32,
    pub h: u32,
}
pub struct Square {
    pub s: u32,
}
impl Shape for Rect {
    fn area(&self) -> u64 {
        self.w as u64 * self.h as u64
    }
}
impl Shape for Square {
    fn area(&self) -> u64 {
        self.s as u64 * self.s as u64
    }
}
pub fn total(shapes: &[&dyn Shape]) -> u64 {
    let mut t = 0u64;
    for s in shapes {
        t = t.saturating_add(s.area());
    }
    t
}
