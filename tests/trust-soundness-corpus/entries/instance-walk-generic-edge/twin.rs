// trust-soundness-corpus entry `instance-walk-generic-edge`, the TWIN (shape of trust
// da8ff46046 tests/ui/trust/unverified_edge_generic_instance_controls.rs `t_generic`):
// the generic dispatches into a LOCAL impl, so the `assume_total` skip is sound and
// the build should be accepted.
#![feature(register_tool)]
#![register_tool(trust)]
#![allow(dead_code)]

pub trait Ok1 {
    fn o(&self) -> u32;
}

impl Ok1 for u32 {
    fn o(&self) -> u32 {
        *self / 2
    }
}

fn gc<T: Ok1>(x: &T) -> u32 {
    x.o()
}

#[trust::assume_total]
#[inline(never)]
pub fn t_generic() -> u32 {
    gc(&5u32)
}
