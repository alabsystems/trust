//! A type whose destructor lives in this (upstream) crate.
pub struct Fd(pub i32);
impl Drop for Fd {
    fn drop(&mut self) {}
}
