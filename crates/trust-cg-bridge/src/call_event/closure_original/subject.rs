#![no_std]

#[unsafe(no_mangle)]
pub extern "C" fn closure_return(value: &mut u64) -> &mut u64 {
    let once = move || value;
    once()
}
