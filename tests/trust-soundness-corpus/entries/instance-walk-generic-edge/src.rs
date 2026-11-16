// trust-soundness-corpus entry `instance-walk-generic-edge` (INSTANCE-WALK-1). The
// claim is `#[trust::assume_total]`'s skip of `t`: the build is accepted as verified
// only if nothing `t` can run is unverified. `g2::<u32>` dispatches to the
// verify-off dependency's `impl Act2 for u32`; the edge enumeration held the local
// generic because its TYPE argument (`u32`) is foundational.
#![feature(register_tool)]
#![register_tool(trust)]
#![allow(dead_code)]
extern crate unverified_edge_instance_dep as dep;
use dep::Act2;

fn g2<T: Act2>(x: &T) -> u32 {
    x.a2()
}

#[trust::assume_total]
#[inline(never)]
pub fn t() -> u32 {
    g2(&5u32)
}
