//@ probe-shape: Projection
//@ probe-expect: discharged
//@ probe-note: POSITIVE, and the twin half of `f84`'s differential. `Boxed` declares
//@ probe-note: exactly one field, `value: u32` — the SAME declared field shape as
//@ probe-note: `core::cell::UnsafeCell<u32>`. It is admitted; `f84` is refused. The one
//@ probe-note: difference between the two programs is interior mutability, so the pair
//@ probe-note: measures that `is_freeze`/K2 is the net doing the refusing rather than
//@ probe-note: some structural rule that would have refused `f84` anyway.
//@ probe-note: Like every view row it is graded BELOW `Certified` (owner ruling R1):
//@ probe-note: `Trusted`/`Constructive`, marker `frozen-shared-erased`, withheld by the
//@ probe-note: authenticated `targo trust` lane.
clean { def id32b (x : UInt32) : UInt32 := x }
pub struct Boxed { pub value: u32 }
impl Boxed {
    pub fn peek(&self) -> u32
        ensures result == id32b(self.value)
    { self.value }
}
