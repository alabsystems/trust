#![no_std]

// Preserve the original three-function FnOnce pointer protocol independently
// of the ordinary four-function memory subject.
#[unsafe(no_mangle)]
pub extern "C" fn leaf_source_anchor(p: &mut u32) -> &mut u32 {
    let take = move || {
        let consumed = p;
        consumed
    };
    take()
}
