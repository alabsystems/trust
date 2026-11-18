#![feature(fn_traits)]
#![no_std]

pub fn zero_capture_once() -> u32 {
    let callback = || 41u32;
    core::ops::FnOnce::call_once(callback, ())
}

pub fn zero_capture_once_receiver_effects() -> u32 {
    let mut evaluations = 0u32;
    let callback = {
        evaluations += 1;
        || 41u32
    };
    let result = core::ops::FnOnce::call_once(callback, ());
    evaluations * 100 + result
}

pub fn zero_capture_direct_fn() -> u32 {
    let callback = || 43u32;
    callback()
}

pub fn zero_capture_direct_fn_mut_request() -> u32 {
    let mut callback = || 47u32;
    core::ops::FnMut::call_mut(&mut callback, ())
}

#[unsafe(no_mangle)]
pub extern "C" fn canary_0() -> u32 {
    zero_capture_once()
}

#[unsafe(no_mangle)]
pub extern "C" fn canary_1() -> u32 {
    zero_capture_once_receiver_effects()
}

#[unsafe(no_mangle)]
pub extern "C" fn canary_2() -> u32 {
    zero_capture_direct_fn()
}

#[unsafe(no_mangle)]
pub extern "C" fn canary_3() -> u32 {
    zero_capture_direct_fn_mut_request()
}

// New proposed controls; these are not part of the historical41/141 input.
#[unsafe(no_mangle)]
pub extern "C" fn once_argument(x: u64) -> u64 {
    core::ops::FnOnce::call_once(|input: u64| input ^ 7, (x,))
}

#[unsafe(no_mangle)]
pub extern "C" fn once_receiver_expression_order() -> u64 {
    let mut order = 0u64;
    let result = core::ops::FnOnce::call_once(
        {
            order = order * 10 + 1;
            |input: u64| input
        },
        ({
            order = order * 10 + 2;
            order
        },),
    );
    order * 100 + result
}
