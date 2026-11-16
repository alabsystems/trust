//@ probe-shape: none
//@ probe-expect: clause-outside-fragment
//@ probe-note: NEGATIVE, must stay red. MEASURED on a stage-1 compiler carrying I1.
//@ probe-note: The body casts the borrow to an address. The view's soundness argument
//@ probe-note: step (d) is that the ADDRESS cannot influence the result — every use of
//@ probe-note: the borrow must be a scalar field read through it — so the builder
//@ probe-note: refuses `Rvalue::AddressOf`, `Rvalue::Ref` and `Rvalue::CopyForDeref`
//@ probe-note: ANYWHERE in the body, not only on the borrow.
//@ probe-note: A body whose value depends on WHERE the pointee lives is not a function
//@ probe-note: of the pointee's values, and the minted equation would be false of it.
clean { def id64e (x : UInt64) : UInt64 := x }
pub struct PointE { pub x: u32, pub y: u32 }
impl PointE {
    pub fn addr(&self) -> u64
        ensures result == id64e(0)
    { self as *const PointE as u64 }
}
