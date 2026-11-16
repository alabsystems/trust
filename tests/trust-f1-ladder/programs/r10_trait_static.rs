trait Area { fn area(&self) -> u64; }
struct Sq(u64); struct Rect(u64, u64);
impl Area for Sq { fn area(&self) -> u64 { self.0 * self.0 } }
impl Area for Rect { fn area(&self) -> u64 { self.0 * self.1 } }
#[inline(never)] fn total<A: Area, B: Area>(a: &A, b: &B) -> u64 { a.area() + b.area() }
#[no_mangle] pub extern "C" fn rung(x: u64) -> u64 { total(&Sq(x), &Rect(x, 3)) }
