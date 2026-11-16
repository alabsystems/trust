trait Area { fn area(&self) -> u64; }
struct Sq(u64); struct Rect(u64, u64);
impl Area for Sq { fn area(&self) -> u64 { self.0 * self.0 } }
impl Area for Rect { fn area(&self) -> u64 { self.0 * self.1 } }
#[inline(never)] fn get(d: &dyn Area) -> u64 { d.area() }
#[no_mangle] pub extern "C" fn rung(x: u64) -> u64 { let s = Sq(x); let r = Rect(x, 3); if x & 1 == 0 { get(&s) } else { get(&r) } }
