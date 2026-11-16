#![feature(type_alias_impl_trait)]
#![allow(dead_code, private_interfaces)]
use std::mem::{ManuallyDrop, MaybeUninit};
union Lookalike {
    unit: (),
    payload: ManuallyDrop<u64>,
}
#[repr(C, align(32))]
struct Aligned([u8; 3]);
type Hidden = impl Copy;
#[define_opaque(Hidden)]
fn hidden() -> Hidden {
    7_u64
}
fn case_scalar(_: MaybeUninit<u64>) {}
fn case_array(_: MaybeUninit<[u64; 2]>) {}
fn case_unit(_: MaybeUninit<()>) {}
fn case_empty_array(_: MaybeUninit<[u64; 0]>) {}
fn case_aligned(_: MaybeUninit<Aligned>) {}
fn case_lookalike(_: Lookalike) {}
fn case_wrapper(_: ManuallyDrop<u64>) {}
fn case_plain(_: Aligned) {}
fn case_pointer(_: *const MaybeUninit<u64>) {}
fn case_generic<T>(_: MaybeUninit<T>) {}
fn case_unrevealed_alias(_: MaybeUninit<Hidden>) {}
fn main() {}
