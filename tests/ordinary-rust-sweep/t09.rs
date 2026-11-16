pub trait Area {
    fn area(&self) -> u64;
}
pub struct Sq(pub u32);
impl Area for Sq {
    fn area(&self) -> u64 {
        (self.0 as u64) * (self.0 as u64)
    }
}
pub fn total<T: Area>(v: &[T]) -> u64 {
    let mut t = 0u64;
    for x in v {
        t = t.saturating_add(x.area());
    }
    t
}
