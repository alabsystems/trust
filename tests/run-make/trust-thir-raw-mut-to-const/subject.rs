#![allow(dead_code)]
#[repr(C)]
pub struct Pair { pub guard: u64, pub value: u64 }
pub fn identity(p: *mut u8) -> *const u8 { p }
pub fn array(p: *mut [u8; 4]) -> *const [u8; 4] { p }
pub fn unit(p: *mut ()) -> *const () { p }
pub fn nested(p: *mut *mut u8) -> *const *mut u8 { p }
pub fn local(p: *mut u64) -> *const u64 { let q: *const u64 = p; q }
pub unsafe fn entry_field(p: *mut Pair) -> u64 {
    let q: *const Pair = p;
    unsafe { (*q).value }
}
pub unsafe fn source_once(p: *mut u8, count: *mut u64) -> *const u8 {
    unsafe { *count = 17; p }
}
pub fn fat(p: *mut [u8]) -> *const [u8] { p }
pub fn unresolved<T: ?Sized>(p: *mut T) -> *const T { p }
pub fn borrowed(p: &mut u8) -> *const u8 { p }
pub fn borrowed_retype(p: &mut Pair) -> *const Pair {
    let raw = p as *mut Pair;
    raw
}
pub fn local_escape() -> *const u64 {
    let mut value = 1u64;
    let raw = &raw mut value;
    raw
}
pub fn pointer_int(p: *mut u8) -> usize { let q: *const u8 = p; q as usize }
pub unsafe fn integer_field(p: usize) -> u64 {
    let p = p as *mut Pair;
    let q: *const Pair = p;
    unsafe { (*q).value }
}
pub unsafe fn write_retyped(p: *mut Pair) {
    let q: *const Pair = p;
    let r = q as *mut Pair;
    unsafe { (*r).value = 7; }
}
pub fn unsafe_fn(p: fn()) -> unsafe fn() { p }
