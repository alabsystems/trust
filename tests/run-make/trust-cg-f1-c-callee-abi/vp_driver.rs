//! Built by the DEFAULT backend; calls `vp`'s function, built by whichever backend is under test.
#![feature(rustc_private)]
extern crate libc;
extern crate vp;

fn main() {
    let mut s: *mut libc::c_void = core::ptr::null_mut();
    let n = vp::f1_format(&mut s, c"v=%d".as_ptr(), 42);
    let text = if s.is_null() {
        String::from("<null>")
    } else {
        unsafe { core::ffi::CStr::from_ptr(s.cast()) }.to_string_lossy().into_owned()
    };
    unsafe { libc::free(s) };
    println!("n={n} text={text}");
}
