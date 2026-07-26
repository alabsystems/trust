// POSITIVE: a root-body monomorphic inherent-method + operator pick.
// Expected: the witness MINTs and warm replay ACCEPTs it, byte-identical to a
// no-flag build. Guards Follow-on 2's supported case (picks whose HirId is in
// the ROOT body, so the checker's `try_resolve` re-derivation actually runs).
pub struct P {
    x: i32,
    y: i32,
}

impl P {
    pub fn sum(&self) -> i32 {
        self.x + self.y
    }
    pub fn add(&self, k: i32) -> i32 {
        self.x + k
    }
}

pub fn use_methods(p: &P) -> i32 {
    let a = p.sum();
    let b = p.add(5);
    if a < b { a } else { b }
}
