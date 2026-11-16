//! Source-to-level-S callable transport control; no machine-code/proof claim.
#![feature(core_intrinsics)]
#![allow(dead_code, internal_features)]
pub fn apply_once<F: FnOnce(u64) -> u64>(f: F, x: u64) -> u64 { f(x) }
pub fn apply_ref<F: Fn(u64) -> u64>(f: &F, x: u64) -> u64 { f(x) }
pub fn apply_mut<F: FnMut(u64) -> u64>(f: &mut F, x: u64) -> u64 { f(x) }
pub fn twice<F: Fn(u64) -> u64>(f: &F, x: u64) -> (u64, u64) { (f(x), f(x)) }
pub fn apply_result<F, R>(f: F, x: u64) -> R where F: FnOnce(u64) -> R { f(x) }
pub fn unit_output<F: FnOnce(u64)>(f: F, x: u64) { f(x) }
pub fn identity<T>(x: T) -> T { x }
pub fn relay<F: FnOnce(u64) -> u64>(f: F, x: u64) -> u64 { apply_once(f, x) }
pub fn two_instances<F, G>(f: F, g: G, x: u64) -> (u64, u64)
where F: FnOnce(u64) -> u64, G: FnOnce(u64) -> u64 { (apply_once(f, x), apply_once(g, x)) }
#[track_caller]
pub fn tracked<T>(x: T) -> T { x }
pub fn tracked_caller<T>(x: T) -> T { tracked(x) }
pub fn dynamic(f: &dyn Fn(u64) -> u64, x: u64) -> u64 { f(x) }
pub fn option_identity<T>(x: Option<T>) -> Option<T> { x }
pub fn option_inspect<T>(x: Option<T>) -> bool { match x { Some(_) => true, None => false } }
pub fn closure_source(x: u64) -> u64 { apply_once(|v| v.wrapping_add(7), x) }

pub fn intrinsic_black_box<T>(x: T) -> T { std::intrinsics::black_box(x) }
