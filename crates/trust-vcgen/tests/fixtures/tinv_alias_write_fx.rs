//! TINV D2 premise rail (plan defect #14): writes through a field alias of `self`.
pub struct P {
    i: u64,
    n: u64,
}

impl P {
    /// The E point: a constructor whose operands the entry assumption on `*self` binds
    /// (a constructor from integer parameters alone is unsituated in v1).
    pub fn dup(&self) -> P {
        P { i: self.i, n: self.n }
    }

    /// (a) unguarded write through `&mut self.i`: `i <= n` is NOT preserved.
    pub fn set(&mut self, v: u64) {
        let r = &mut self.i;
        *r = v;
    }

    /// (b) guarded write through `&mut self.i`: `i <= n` IS preserved.
    pub fn set_guarded(&mut self, v: u64) {
        if v <= self.n {
            let r = &mut self.i;
            *r = v;
        }
    }

    /// (c) the alias passed to an in-crate helper.
    pub fn set_via(&mut self, v: u64) {
        put(&mut self.i, v);
    }
}

pub fn put(r: &mut u64, v: u64) {
    *r = v;
}
