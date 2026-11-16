#![no_std]

// Preserve the independent source closure/frame boundary after primitive
// source modules no longer need this anchor to select the native compiler.
#[unsafe(no_mangle)]
pub extern "C" fn trust_c_u8_source_anchor(x: &mut u32) -> &mut u32 {
    let take = move || { let consumed = x; consumed };
    take()
}
