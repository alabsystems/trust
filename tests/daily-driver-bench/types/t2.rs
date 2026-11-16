pub trait S { fn a(&self) -> u32; } pub struct Q(pub u32); impl S for Q { fn a(&self) -> u32 { self.0 } } pub fn f(q: &Q) -> u32 { q.a() }
