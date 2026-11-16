//! A local `Drop` impl whose body is empty, and a function that drops a value of it. With the
//! drop-glue lane active (the strict output gate), `make`'s `Inst::Drop` is resolved to a call of
//! the synthesized `drop_glue::<T>`; the converter (`real_calls=false`) then refuses that CALL,
//! never the `Drop` (increment 5 brings real calls).
pub struct T(pub u32);
impl Drop for T {
    #[inline(never)]
    fn drop(&mut self) {}
}
#[inline(never)]
pub fn make(x: u32) -> u32 {
    let _t = T(x);
    x ^ 1
}
