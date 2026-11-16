// A shared Vec header does not freeze its buffer through a previously derived raw pointer.
// The two element references are temporary and dead before the nullary call writes.
static mut SAVED: *mut u32 = std::ptr::null_mut();
#[inline(never)]
fn mutate_saved_buffer() { unsafe { SAVED.write(99); } }
#[inline(never)]
fn compare(v: &Vec<u32>) -> bool {
    let before = v[0];
    mutate_saved_buffer();
    before == v[0]
}
fn main() {
    let mut v = vec![7];
    unsafe { SAVED = v.as_mut_ptr(); }
    assert!(!compare(&v));
    assert_eq!(v[0], 99);
}
