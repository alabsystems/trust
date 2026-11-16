// offloads_to_check is semantic state consumed after typeck. Unlike the
// error-only potentially_region_dependent_goals, it must block witness minting
// until it has an independently validated encoding. Avoid an explicit turbofish:
// user_provided_types would independently refuse this fixture and hide the gap.
#![feature(core_intrinsics)]
#![allow(internal_features)]

fn kernel(x: u32) -> u32 {
    x
}

pub fn offload_u32(x: u32) -> u32 {
    core::intrinsics::offload(kernel, [1, 1, 1], [1, 1, 1], 0, -1, (x,))
}
