#![no_std]

#[unsafe(no_mangle)]
pub extern "C" fn closure_write(value: &mut u64, delta: u8) -> u64 {
    let once = move || {
        let target = value;
        *target += delta as u64;
        *target
    };
    once()
}

#[unsafe(no_mangle)]
pub extern "C" fn closure_return(value: &mut u64) -> &mut u64 {
    let once = move || value;
    once()
}
