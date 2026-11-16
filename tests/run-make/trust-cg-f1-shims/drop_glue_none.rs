// `drop_in_place::<u64>` reified: `DropGlue(u64, None)` is collected only when it is not a direct
// call.
pub fn get() -> unsafe fn(*mut u64) {
    let f: unsafe fn(*mut u64) = core::ptr::drop_in_place::<u64>;
    f
}
