//! A packed struct with a needs-drop field: rustc moves the field to an aligned temporary before
//! dropping it, which this cut does not synthesize.
pub struct T(pub u32);
impl Drop for T {
    fn drop(&mut self) {}
}
#[repr(packed)]
pub struct P {
    pub b: u8,
    pub t: T,
}
#[inline(never)]
pub fn mk(x: u32) -> u32 {
    let _p = P { b: 1, t: T(x) };
    x ^ 3
}
