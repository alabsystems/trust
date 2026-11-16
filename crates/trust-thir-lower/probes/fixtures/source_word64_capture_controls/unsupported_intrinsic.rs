#![feature(core_intrinsics)]
fn original_add(a:u64,b:u64)->u64 { core::intrinsics::wrapping_sub(a,b) }
