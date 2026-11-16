// trust-soundness-corpus entry `instance-walk-generic-edge` (INSTANCE-WALK-1): the
// dependency, built with verification OFF (as Targo builds every dependency unit).
// Its impl for the foundational type `u32` writes through null, so any caller that
// can reach it is not total. Shape of trust da8ff46046
// tests/ui/trust/auxiliary/unverified_edge_instance_dep.rs, with the crashing impl
// its BEFORE measurement used.
pub trait Act2 {
    fn a2(&self) -> u32;
}

impl Act2 for u32 {
    fn a2(&self) -> u32 {
        unsafe { core::ptr::write_volatile(core::ptr::null_mut::<u32>(), *self) };
        1
    }
}
