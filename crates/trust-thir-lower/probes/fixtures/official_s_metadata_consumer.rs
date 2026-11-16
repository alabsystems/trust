extern crate official_template_fixture as upstream;
pub fn use_identity(x: u64) -> u64 { upstream::identity(x) }
pub fn use_relay(x: u64) -> u64 { upstream::relay(x) }
pub fn use_slots(x: u64) -> u64 { upstream::slots::<u64, 9>(x) }
pub fn use_scalar_const() -> u64 { upstream::scalar_const::<{u64::MAX}>() }
pub fn use_const_relay() -> u64 { upstream::const_relay::<{u64::MAX}>() }
pub fn use_mix(x: u64) -> u64 { upstream::mix(x) }
pub fn use_twice(x: u64) -> u64 { upstream::twice(x) }
pub fn use_tracked(x: u64) -> u64 { upstream::tracked(x) }
pub fn use_overflow(x: u64) -> u64 { upstream::overflow::<u8>(x) }
pub fn use_apply_once(x: u64) -> u64 { upstream::apply_once(|n| n, x) }
pub fn use_apply_ref(x: u64) -> u64 { upstream::apply_ref(&|n| n, x) }
pub fn use_apply_mut(x: u64) -> u64 { upstream::apply_mut(&mut |n| n, x) }
