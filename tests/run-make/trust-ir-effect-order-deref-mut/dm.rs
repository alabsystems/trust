#![crate_name = "dm"]
unsafe extern "C" { fn close(fd: i32) -> i32; }
#[inline(never)] fn c(fd: i32) -> i32 { unsafe { close(fd) } }
pub struct Inner { pub n: i32 }
pub struct Outer { pub inner: Inner }
impl std::ops::Deref for Outer { type Target = Inner; fn deref(&self) -> &Inner { &self.inner } }
impl std::ops::DerefMut for Outer {
    fn deref_mut(&mut self) -> &mut Inner { unsafe { close(-1) }; &mut self.inner }
}
pub fn set_n(o: &mut Outer, fd: i32) { o.n = c(fd); }
pub fn set_pure(o: &mut Outer, fd: i32) { o.n = fd; }
